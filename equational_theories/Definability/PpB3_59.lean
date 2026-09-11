import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3926`: `x ◇ y = (x ◇ (y ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3926 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3926 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3926.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X0)) X2 X3
       have i₂ := eq14 X0 X1 (M.op X2 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq59 X0 X1 x X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq68 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) := by
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
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq83 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq222 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq61
    | (have j0 := eq61 x y X0
       grind)
    | exact resolve eq61 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq61
    | (have j0 := eq61 (σ x) (σ y) X0
       grind)
    | exact resolve eq61 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq222 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq222 (M.op x y)
       grind)
    | exact resolve eq13 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq271 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq223 eq12
    | (have j0 := eq12 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 X0 (M.op (σ x) (σ y))
       have r₂ := eq223 X0
       grind)
    | exact resolve eq12 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq223 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq223 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq275 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq271 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq309 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq318 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq243 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq320 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq318 eq130
    | exact resolve eq130 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq318
  have eq324 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq320
    | exact resolve eq320 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq327 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq324 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq328 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq327
  have eq331 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq328 eq61
    | exact resolve eq61 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq328
  have eq355 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have j0 := eq273 (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq741 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq309 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq309
    | (have j0 := eq309 y X0
       grind)
    | exact resolve eq309 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq20 eq309
    | (have j0 := eq309 (M.op x y) X0
       grind)
    | exact resolve eq309 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ x) (σ y)))) ∨ (σ X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq275 eq309
    | (have j1 := eq275 (σ X0)
       grind)
    | exact resolve eq309 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq309
  have eq760 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 ∨ (σ X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq751 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq751
    | (have j0 := eq751 X0
       grind)
    | exact resolve eq751 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq1064 : y = (τ (k (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq760 eq741
    | (have j1 := eq760 y
       grind)
    | exact resolve eq741 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq1065 : (M.op x y) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq760 eq742
    | (have j1 := eq760 (M.op x y)
       grind)
    | exact resolve eq742 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq760
  have eq1073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq20 eq1065
    | exact resolve eq1065 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1074 : y = (τ (k (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1064
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1064
    | exact resolve eq1064 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1082 : (M.op x y) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | (have r₁ := eq1073
       have r₂ := eq27
       grind)
    | exact resolve eq1073 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1087 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1082 eq15
    | exact resolve eq15 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1102 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq1087
    | exact resolve eq1087 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq2259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2259
    | exact resolve eq2259 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259
  have eq2263 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2260
       have r₂ := eq27
       grind)
    | exact resolve eq2260 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq2265 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2263
    | exact resolve eq2263 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq2267 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2265
    | exact resolve eq2265 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265
  have eq2270 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2267 eq51
    | (have r₁ := eq51
       have r₂ := eq2267
       grind)
    | exact resolve eq51 eq2267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2267
  have eq2288 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2270
  have eq2462 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2288 eq83
    | exact resolve eq83 eq2288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2288
  have eq2470 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq2462
    | exact resolve eq2462 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2462
  have eq2474 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2470
       have r₂ := eq50
       grind)
    | exact resolve eq2470 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2470
  have eq2477 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq2474
       grind)
    | exact superpose eq2474 eq76
    | exact resolve eq76 eq2474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2478 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq2474
       grind)
    | exact superpose eq2474 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq2474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2474
  have eq2479 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2478
  have eq2481 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2479
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2479
    | exact resolve eq2479 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2482 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2481
  have eq2483 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2477
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2477
    | exact resolve eq2477 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477
  have eq2486 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2482
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2482
    | exact resolve eq2482 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482
  have eq2557 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2486 eq27
    | exact resolve eq27 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2564 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2486 eq355
    | exact resolve eq355 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq2571 : y = (τ (k (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2486 eq1074
    | exact resolve eq1074 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq2486
  have eq2578 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq83 eq2571
    | exact resolve eq2571 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq2571
  have eq2580 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2578
       have r₂ := eq68
       grind)
    | exact resolve eq2578 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq2578
  have eq2653 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2483 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2483
  have eq2654 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2653
  have eq2658 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2654
    | exact resolve eq2654 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2654
  have eq2659 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2658
  have eq2664 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2659
    | exact resolve eq2659 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2659
  have eq2666 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2664 eq27
    | exact resolve eq27 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2664
  have eq2812 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq2580
       grind)
    | exact superpose eq2580 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq2580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580
  have eq2813 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2812
  have eq2815 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2813
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2813
    | exact resolve eq2813 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2813
  have eq2816 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq2815
  have eq2821 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2816
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2816
    | exact resolve eq2816 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2816
  have eq2830 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2821 eq102
    | exact resolve eq102 eq2821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq2821
  have eq2858 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2830
  have eq3217 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2858 eq2564
    | exact resolve eq2564 eq2858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2564 eq2858
  have eq3221 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3217
  have eq3225 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3221
       have r₂ := eq2557
       grind)
    | exact resolve eq3221 eq2557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557 eq3221
  have eq3227 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3225 eq20
    | exact resolve eq20 eq3225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3229 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3225 eq50
    | (have r₁ := eq50
       have r₂ := eq3225
       grind)
    | exact resolve eq50 eq3225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq3225
  have eq3259 : x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq3229
  have eq3272 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3227
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3227
    | exact resolve eq3227 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3227
  have eq3402 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3272 eq2666
    | (have r₁ := eq2666
       have r₂ := eq3272
       grind)
    | exact resolve eq2666 eq3272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2666
  have eq3414 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3402
  have eq3415 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3414
  have eq3444 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3415 eq27
    | exact resolve eq27 eq3415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3461 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3415 eq1102
    | exact resolve eq1102 eq3415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq3415
  have eq3785 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq3259
       grind)
    | exact superpose eq3259 eq76
    | exact resolve eq76 eq3259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq3259
  have eq3791 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3785
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3785
    | exact resolve eq3785 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3785
  have eq3940 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3272 eq3791
    | exact resolve eq3791 eq3272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3272 eq3791
  have eq3958 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3940
  have eq4104 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3958 eq3461
    | exact resolve eq3461 eq3958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3461 eq3958
  have eq4110 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq4104
  have eq4116 : x = (M.op x y) := by
    first
    | (have r₁ := eq4110
       have r₂ := eq3444
       grind)
    | exact resolve eq4110 eq3444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3444 eq4110
  have eq4121 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq4116 eq20
    | exact resolve eq20 eq4116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4116
  have eq4164 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4121
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4121
    | exact resolve eq4121 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4121
  have eq4166 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq4164 eq26
    | exact resolve eq26 eq4164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4164
  have eq4210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq331 eq4166
    | exact resolve eq4166 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq4166
  have eq4216 : False := by grind
  exact eq4216

/-- `Equation3926`: `x ◇ y = (x ◇ (y ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_y_x_pyx_Equation3926 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3926 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3926.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X0)) X2 X3
       have i₂ := eq14 X0 X1 (M.op X2 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq59 X0 X1 x X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (M.op X0 (M.op X1 X0)) X2) = X2 ∨ (k X2 (M.op X0 (M.op X1 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op X1 X0))
       have i₂ := eq14 X0 X1 (M.op X0 (M.op X1 X0))
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op X1 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 X1) = X2 ∨ (k X2 (M.op X0 (M.op X1 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq68
    | (have j0 := eq68 X0 X1 X2
       grind)
    | exact resolve eq68 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq78 : (σ (k y (k y x))) = (k (σ y) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq36 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq36
    | exact resolve eq36 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq127 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq127 eq16
    | exact resolve eq16 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq61
    | (have j0 := eq61 x y X0
       grind)
    | exact resolve eq61 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq61
    | (have j0 := eq61 (σ x) (σ y) X0
       grind)
    | exact resolve eq61 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X1)
       have i₂ := eq61 X0 X1 X2
       grind)
    | exact superpose eq61 eq13
    | (have j0 := eq13 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 (M.op X0 X1) (M.op X0 X1)
       have r₂ := eq61 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq221 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq221 (M.op x y)
       grind)
    | exact resolve eq13 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op (M.op x y) X0) = X0 ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq221 eq12
    | (have j0 := eq12 X0 (M.op x y)
       grind)
    | (have r₁ := eq12 X0 (M.op x y)
       have r₂ := eq221 (M.op x y)
       grind)
    | exact resolve eq12 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq244 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq246 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq221 eq245
    | (have j0 := eq245 X0
       grind)
    | exact resolve eq245 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq245
  have eq261 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq34
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq34 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq222 eq12
    | (have j0 := eq12 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 X0 (M.op (σ x) (σ y))
       have r₂ := eq222 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq12 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq275 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq277 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq222 eq276
    | (have j0 := eq276 X0
       grind)
    | exact resolve eq276 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq276
  have eq309 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq318 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq242 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq318 eq127
    | exact resolve eq127 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq325 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq321
    | exact resolve eq321 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq328 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq325 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq329 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq328
  have eq332 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq329 eq61
    | exact resolve eq61 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 ∨ (k X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq329 eq69
    | exact resolve eq69 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq481 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq454 X0
       grind)
    | (have r₁ := eq454 X0
       have r₂ := eq329
       grind)
    | exact resolve eq454 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq500 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq329 eq481
    | (have j0 := eq481 X0
       grind)
    | exact resolve eq481 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq481
  have eq566 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq83 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq568 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq566 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq584 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op x y))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq41 eq500
    | (have j0 := eq500 (σ X0)
       grind)
    | exact resolve eq500 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq500
  have eq764 : ∀ X0 : G, (k (k y x) (τ X0)) = (τ (k (k (σ y) (σ x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq309 (k y x) X0
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq309
    | exact resolve eq309 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq309 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq309
    | (have j0 := eq309 y X0
       grind)
    | exact resolve eq309 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq20 eq309
    | (have j0 := eq309 (M.op x y) X0
       grind)
    | exact resolve eq309 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ x) (σ y)))) ∨ (σ X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq277 eq309
    | (have j1 := eq277 (σ X0)
       grind)
    | exact resolve eq309 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq309
  have eq791 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 ∨ (σ X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq780 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq780
    | (have j0 := eq780 X0
       grind)
    | exact resolve eq780 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq832 : (k y (k y x)) = (τ (k (σ y) (k (σ y) (σ x)))) := by
    first
    | exact superpose eq82 eq771
    | exact resolve eq771 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq1068 : (M.op x y) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq791 eq772
    | (have j1 := eq791 (M.op x y)
       grind)
    | exact resolve eq772 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq20 eq1068
    | exact resolve eq1068 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1085 : (M.op x y) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | (have r₁ := eq1076
       have r₂ := eq27
       grind)
    | exact resolve eq1076 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1090 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1085 eq15
    | exact resolve eq15 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1105 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq1090
    | exact resolve eq1090 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1257 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq234 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq4565 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq568 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq568
    | (have j0 := eq568 (τ X0)
       grind)
    | exact resolve eq568 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq568
  have eq4587 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4565 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4565
    | (have j0 := eq4565 X0
       grind)
    | exact resolve eq4565 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4565
  have eq4596 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4587 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4587
    | (have j0 := eq4587 X0
       grind)
    | exact resolve eq4587 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4587
  have eq5874 : ∀ X0 : G, (k (k (σ (M.op x y)) (M.op (σ x) (σ y))) (σ X0)) = (σ (M.op X0 (M.op x y))) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1085 eq261
    | (have j0 := eq261 X0 x
       grind)
    | exact resolve eq261 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq5929 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (M.op X0 (M.op x y))) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1105 eq5874
    | (have j0 := eq5874 X0
       grind)
    | exact resolve eq5874 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5874
  have eq5934 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (M.op X0 (M.op x y))) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq37 eq5929
    | (have j0 := eq5929 X0
       grind)
    | exact resolve eq5929 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq5929
  have eq5947 : (σ (M.op x y)) = (σ (M.op (τ (M.op (σ x) (σ y))) (M.op x y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq791 eq5934
    | (have j0 := eq5934 (τ (M.op (σ x) (σ y)))
       have j1 := eq791 (M.op x y)
       grind)
    | exact resolve eq5934 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq5934
  have eq6068 : (σ (M.op x y)) = (σ (M.op (τ (M.op (σ x) (σ y))) (M.op x y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5947
    | exact resolve eq5947 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5947
  have eq6074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (M.op (τ (M.op (σ x) (σ y))) (M.op x y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq20 eq6068
    | exact resolve eq6068 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6068
  have eq6077 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ (M.op (τ (M.op (σ x) (σ y))) (M.op x y))) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | (have r₁ := eq6074
       have r₂ := eq27
       grind)
    | exact resolve eq6074 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6074
  have eq6640 : ∀ X0 : G, (σ (M.op x y)) = (σ (M.op (τ (M.op (σ x) (σ y))) (M.op x y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) X0) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq6077 eq61
    | exact resolve eq61 eq6077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6077
  have eq6655 : ∀ X0 : G, (τ (σ (M.op x y))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) X0) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq6640 eq16
    | (have j1 := eq6640 X0
       grind)
    | exact resolve eq16 eq6640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6640
  have eq6679 : ∀ X0 : G, (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) X0) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30 eq6655
    | (have j0 := eq6655 X0
       grind)
    | exact resolve eq6655 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq6655
  have eq6680 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) X0) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq6679 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6679
  have eq6686 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op (τ (M.op (σ x) (σ y))) X0) = X0 ∨ (k X0 (τ (M.op (σ x) (σ y)))) = X0 ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq6680 eq12
    | (have j0 := eq12 X0 (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq12 X0 (τ (M.op (σ x) (σ y)))
       have r₂ := eq6680 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq12 eq6680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6680
  have eq6703 : ∀ X0 : G, (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (k X0 (τ (M.op (σ x) (σ y)))) = X0 ∨ (M.op (τ (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6686 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6686
  have eq11579 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (τ (M.op (σ x) (σ y))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (k X0 (τ (M.op (σ x) (σ y)))) = X0 ∨ (M.op (τ (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq6703 (M.op x X0)
       grind)
    | exact superpose eq6703 eq13
    | (have j0 := eq13 (M.op x y) (τ (M.op (σ x) (σ y)))
       have j1 := eq6703 X0
       grind)
    | (have r₁ := eq13 (M.op x y) (τ (M.op (σ x) (σ y)))
       have r₂ := eq6703 X0
       grind)
    | (have r₁ := eq13 X0 (τ (M.op (σ x) (σ y)))
       have r₂ := eq6703 X0
       grind)
    | exact resolve eq13 eq6703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6703
  have eq11591 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (k X0 (τ (M.op (σ x) (σ y)))) = X0 ∨ (M.op (τ (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11579 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11579
  have eq11600 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (k X0 (τ (M.op (σ x) (σ y)))) = X0 ∨ (M.op (τ (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq772 eq11591
    | (have j0 := eq11591 X0
       grind)
    | exact resolve eq11591 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772 eq11591
  have eq11606 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (τ (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1085 eq11600
    | (have j0 := eq11600 X0
       grind)
    | exact resolve eq11600 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11600
  have eq12141 : (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq11606 eq4596
    | (have j0 := eq4596 (τ (M.op (σ x) (σ y)))
       have j1 := eq11606 (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq4596 (τ (M.op (σ x) (σ y)))
       have r₂ := eq11606 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq4596 eq11606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4596 eq11606
  have eq12168 : (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq12141
  have eq12169 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq12168
  have eq12228 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) X0) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq12169 eq61
    | exact resolve eq61 eq12169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12169
  have eq22685 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq22685
    | exact resolve eq22685 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22685
  have eq22698 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq22693
       have r₂ := eq27
       grind)
    | exact resolve eq22693 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22693
  have eq22700 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq22698
    | exact resolve eq22698 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22698
  have eq29810 : (k (k y x) (M.op x y)) = (τ (k (k (σ y) (σ x)) (k (σ (M.op x y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1085 eq764
    | exact resolve eq764 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq1085
  have eq29915 : (k (k y x) (M.op x y)) = (τ (k (k (σ y) (σ x)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1105 eq29810
    | exact resolve eq29810 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105 eq29810
  have eq29979 : (τ (k (σ (M.op x y)) (σ (M.op x y)))) = (k (k y x) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq100 eq29915
    | exact resolve eq29915 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq29915
  have eq30040 : (k (M.op x y) (M.op x y)) = (k (k y x) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq150 eq29979
    | exact resolve eq29979 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq29979
  have eq30045 : (M.op x y) = (k (k y x) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq318 eq30040
    | exact resolve eq30040 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq30040
  have eq67956 : (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30045 eq246
    | (have j0 := eq246 (k y x)
       grind)
    | exact resolve eq246 eq30045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq30045
  have eq67962 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq67956
  have eq1189859 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq22700 eq61
    | exact resolve eq61 eq22700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22700
  have eq1189899 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1189859
    | (have j0 := eq1189859 (σ y)
       grind)
    | exact resolve eq1189859 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189859
  have eq1191903 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1257 x x
       have i₂ := eq1189899
       grind)
    | exact superpose eq1189899 eq1257
    | exact resolve eq1257 eq1189899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257 eq1189899
  have eq1199172 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq567 x x
       have i₂ := eq1191903
       grind)
    | exact superpose eq1191903 eq567
    | (have j0 := eq567 x x
       grind)
    | exact resolve eq567 eq1191903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq1191903
  have eq1199232 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1199172
  have eq1199233 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1199232
  have eq1199262 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1199233
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1199233
    | exact resolve eq1199233 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199233
  have eq1201705 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1199262 eq61
    | exact resolve eq61 eq1199262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199262
  have eq1208205 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1201705 eq26
    | (have j1 := eq1201705 (σ y)
       grind)
    | exact resolve eq26 eq1201705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201705
  have eq1208314 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1208205
  have eq1208329 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1208314 eq51
    | (have r₁ := eq51
       have r₂ := eq1208314
       grind)
    | exact resolve eq51 eq1208314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1208314
  have eq1209907 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1208329
  have eq1218124 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1209907 eq82
    | exact resolve eq82 eq1209907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209907
  have eq1218184 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq1218124
    | exact resolve eq1218124 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218124
  have eq1218191 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1218184
       have r₂ := eq50
       grind)
    | exact resolve eq1218184 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1218184
  have eq1219936 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq1218191
       grind)
    | exact superpose eq1218191 eq75
    | exact resolve eq75 eq1218191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1219937 : (σ (k y x)) = (k (σ y) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq1218191
       grind)
    | exact superpose eq1218191 eq78
    | exact resolve eq78 eq1218191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1218191
  have eq1220066 : (k (σ y) (σ x)) = (k (σ y) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1219937
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq1219937
    | exact resolve eq1219937 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1219937
  have eq1220067 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1219936
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1219936
    | exact resolve eq1219936 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219936
  have eq1220214 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1220067 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq1220067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220067
  have eq1220248 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1220214
    | exact resolve eq1220214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220214
  have eq1220249 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1220248
  have eq1220258 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1220249
    | exact resolve eq1220249 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220249
  have eq1228233 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1220258 eq61
    | exact resolve eq61 eq1220258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220258
  have eq1231392 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1228233 eq26
    | (have j1 := eq1228233 (σ y)
       grind)
    | exact resolve eq26 eq1228233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228233
  have eq1231502 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1231392
  have eq1231516 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1231502 eq27
    | exact resolve eq27 eq1231502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231502
  have eq1624266 : (k y (k y x)) = (τ (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1220066 eq832
    | exact resolve eq832 eq1220066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq1220066
  have eq1624791 : (k y x) = (k y (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq82 eq1624266
    | exact resolve eq1624266 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1624266
  have eq1624803 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1624791
       have i₂ := eq67962
       grind)
    | exact superpose eq67962 eq1624791
    | exact resolve eq1624791 eq67962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67962 eq1624791
  have eq1624890 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq242 y
       grind)
    | (have r₁ := eq1624803
       have r₂ := eq242 (k y (M.op x y))
       grind)
    | (have r₁ := eq1624803
       have r₂ := eq242 y
       grind)
    | exact resolve eq1624803 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq1624803
  have eq1625027 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1624890 eq584
    | (have j0 := eq584 y
       grind)
    | exact resolve eq584 eq1624890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq1624890
  have eq1625126 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1625027
    | exact resolve eq1625027 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625027
  have eq1625127 : (σ y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1625126
  have eq1625170 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1625127
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1625127
    | exact resolve eq1625127 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1625127
  have eq1625188 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1625170
       have r₂ := eq1231516
       grind)
    | exact resolve eq1625170 eq1231516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231516 eq1625170
  have eq1625744 : ∀ X0 : G, x = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x x x
       have i₂ := eq1625188
       grind)
    | exact superpose eq1625188 eq61
    | exact resolve eq61 eq1625188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1625188
  have eq1626066 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1625744 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1625744
    | (have j0 := eq1625744 y
       grind)
    | exact resolve eq1625744 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625744
  have eq1626931 : ∀ X0 : G, (τ (σ x)) = (M.op (τ (σ x)) X0) ∨ (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1626066 eq12228
    | exact resolve eq12228 eq1626066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12228 eq1626066
  have eq1630380 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq1626931
    | exact resolve eq1626931 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626931
  have eq1632167 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq1630380
    | (have j0 := eq1630380 y
       grind)
    | exact resolve eq1630380 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1630380
  have eq1632168 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1632167 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632167
  have eq1633817 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1632168 y
       grind)
    | exact superpose eq1632168 eq18
    | (have j1 := eq1632168 y
       grind)
    | exact resolve eq18 eq1632168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1632168
  have eq1633960 : x = (M.op x y) := by grind
  clear eq1633817
  have eq1633980 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1633960 eq20
    | exact resolve eq20 eq1633960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1633960
  have eq1634931 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1633980
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1633980
    | exact resolve eq1633980 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1633980
  have eq1634933 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1634931 eq26
    | exact resolve eq26 eq1634931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1634931
  have eq1635545 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq332 eq1634933
    | exact resolve eq1634933 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq1634933
  have eq1635642 : False := by grind
  exact eq1635642

/-- `Equation3926`: `x ◇ y = (x ◇ (y ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_x_y_pyx_Equation3926 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3926 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3926.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k (k x X0) X1)) = (k (k (σ x) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k x X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
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
  have eq58 : ∀ X0 X1 : G, (σ (k (k X0 x) X1)) = (k (k (σ X0) (σ x)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 x) X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq10
    | exact resolve eq10 eq39
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
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 (M.op X1 X0)) X2 X3
       have i₂ := eq16 X0 X1 (M.op X2 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 X0 X1 x X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq190 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq179 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 x y X0
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq179
    | (have j0 := eq179 (σ x) (σ y) X0
       grind)
    | exact resolve eq179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X2 (M.op X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X1)
       have i₂ := eq179 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq179 eq13
    | (have j0 := eq13 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq179 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq202 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq207 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq190 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq190 (M.op x y)
       grind)
    | exact resolve eq13 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq211 : ∀ X0 : G, (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq207 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq213 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq191 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 X0 (M.op (σ x) (σ y))
       have r₂ := eq191 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq217 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq213 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq222 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq211 eq37
    | exact resolve eq37 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq222
    | exact resolve eq222 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq228 : (σ x) = (k (σ x) (σ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq217 eq35
    | exact resolve eq35 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (σ x) = (k (σ x) (σ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq228
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq228
    | exact resolve eq228 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq431 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq435 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq447 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq476 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq738 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (M.op X1 X2)
       have i₂ := eq205 X1 X2 (τ X0)
       grind)
    | exact superpose eq205 eq34
    | exact resolve eq34 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq217 eq34
    | exact resolve eq34 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq741 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq741
    | exact resolve eq741 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq773 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq738 X0 X1 X2
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq738
    | exact resolve eq738 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq792 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq770 eq34
    | exact resolve eq34 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq811 : ∀ X0 : G, (k X0 (σ (σ (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq792 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq792
    | exact resolve eq792 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq857 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq811 eq34
    | exact resolve eq34 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq876 : ∀ X0 : G, (k X0 (σ (σ (σ (M.op (σ x) (σ y)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq857 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq857
    | exact resolve eq857 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq935 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (σ (M.op X1 X2))
       have i₂ := eq773 (τ X0) X1 X2
       grind)
    | exact superpose eq773 eq34
    | exact resolve eq34 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq954 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq935 X0 X1 X2
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq935
    | exact resolve eq935 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq978 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op (σ x) (σ y))))))) := by
    intro X0
    first
    | exact superpose eq876 eq34
    | exact resolve eq34 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq997 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (M.op (σ x) (σ y))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq978 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq978
    | exact resolve eq978 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq1045 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1092 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq223 eq477
    | (have j0 := eq477 (σ (M.op x y))
       grind)
    | (have r₁ := eq477 (σ (M.op x y))
       have r₂ := eq223
       grind)
    | exact resolve eq477 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq1093 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1092
  have eq1107 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq1093 eq179
    | exact resolve eq179 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1374 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (σ (σ (M.op X1 X2)))
       have i₂ := eq954 (τ X0) X1 X2
       grind)
    | exact superpose eq954 eq34
    | exact resolve eq34 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1394 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (M.op X1 X2))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1374 X0 X1 X2
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1374
    | exact resolve eq1374 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq1419 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op (σ x) (σ y)))))))) := by
    intro X0
    first
    | exact superpose eq997 eq34
    | exact resolve eq34 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1439 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ (M.op (σ x) (σ y)))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1419 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1419
    | exact resolve eq1419 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq1610 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1045 X0 (M.op X1 X2)
       have i₂ := eq205 X1 X2 (σ X0)
       grind)
    | exact superpose eq205 eq1045
    | exact resolve eq1045 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq1623 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq217 eq1045
    | exact resolve eq1045 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq1045
  have eq1649 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1623 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1623
    | exact resolve eq1623 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq1662 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1610 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1610
    | exact resolve eq1610 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq1688 : (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1649 eq477
    | (have j0 := eq477 (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq477 (τ (M.op (σ x) (σ y)))
       have r₂ := eq1649 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq477 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq1697 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by grind
  clear eq1688
  have eq1778 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq443
       grind)
    | exact superpose eq443 eq39
    | exact resolve eq39 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1779 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1778
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1778
    | exact resolve eq1778 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778
  have eq1781 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1779
    | exact resolve eq1779 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq1869 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq1697 eq179
    | exact resolve eq179 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697
  have eq2867 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op X1 X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (σ (σ (σ (M.op X1 X2))))
       have i₂ := eq1394 (τ X0) X1 X2
       grind)
    | exact superpose eq1394 eq34
    | exact resolve eq34 eq1394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1394
  have eq2888 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (σ (M.op X1 X2)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2867 X0 X1 X2
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq2867
    | exact resolve eq2867 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2867
  have eq4934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1781 eq447
    | exact resolve eq447 eq1781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781
  have eq4943 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq4934
       have r₂ := eq27
       grind)
    | exact resolve eq4934 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4934
  have eq5071 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq4943 eq1662
    | exact resolve eq1662 eq4943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4943
  have eq5102 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq5071
    | exact resolve eq5071 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5071
  have eq5111 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5102 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq5102 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq5102 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5102
  have eq5123 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq5111 x
       grind)
    | exact superpose eq5111 eq35
    | exact resolve eq35 eq5111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq5124 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq443
       have i₂ := eq5111 y
       grind)
    | exact superpose eq5111 eq443
    | exact resolve eq443 eq5111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5111
  have eq5130 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5124
  have eq5141 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5123
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5123
    | exact resolve eq5123 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5123
  have eq5154 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq179 x x x
       have i₂ := eq5130
       grind)
    | exact superpose eq5130 eq179
    | exact resolve eq179 eq5130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5167 : ∀ X0 : G, (k X0 (σ (σ x))) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq954 X0 x x
       have i₂ := eq5130
       grind)
    | exact superpose eq5130 eq954
    | exact resolve eq954 eq5130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq5130
  have eq5199 : ∀ X0 : G, (k X0 (σ (σ x))) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5167 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5167
    | (have j0 := eq5167 X0
       grind)
    | exact resolve eq5167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5167
  have eq5217 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5141 eq475
    | (have j0 := eq475 (σ x) (σ x)
       grind)
    | (have r₁ := eq475 (σ x) (σ x)
       have r₂ := eq5141
       grind)
    | exact resolve eq475 eq5141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq5141
  have eq5218 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5217
  have eq5219 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5218
  have eq5276 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5154 y
       grind)
    | exact superpose eq5154 eq18
    | (have j1 := eq5154 y
       grind)
    | exact resolve eq18 eq5154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5154
  have eq5357 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5276 eq435
    | (have r₁ := eq435
       have r₂ := eq5276
       grind)
    | exact resolve eq435 eq5276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq5408 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5357
  have eq5442 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5219 eq179
    | exact resolve eq179 eq5219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5472 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ x)))))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5219 eq2888
    | exact resolve eq2888 eq5219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5219
  have eq5503 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5442 eq26
    | (have j1 := eq5442 (σ y)
       grind)
    | exact resolve eq26 eq5442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5442
  have eq5636 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5503
  have eq6181 : (σ (σ x)) ≠ (σ (σ x)) ∨ (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5199 eq477
    | (have j0 := eq477 (σ (σ x))
       grind)
    | (have r₁ := eq477 (σ (σ x))
       have r₂ := eq5199 (σ (σ x))
       grind)
    | exact resolve eq477 eq5199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5199
  have eq6200 : (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6181
  have eq7532 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ (σ x))))))) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6200 eq2888
    | exact resolve eq2888 eq6200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2888 eq6200
  have eq8765 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5408 eq107
    | exact resolve eq107 eq5408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq5408
  have eq8778 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq8765
    | exact resolve eq8765 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8765
  have eq8801 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (k x (σ (σ (σ (σ (σ x)))))) X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7532 eq43
    | exact resolve eq43 eq7532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq7532
  have eq8822 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (k (M.op x y) (σ (σ (σ (σ (σ x)))))) X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq5276 eq8801
    | exact resolve eq8801 eq5276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8801
  have eq8838 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq5472 eq8822
    | exact resolve eq8822 eq5472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5472 eq8822
  have eq8845 : ∀ X0 : G, (k (σ x) (σ X0)) = (k (σ (M.op x y)) (σ X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq8838
    | exact resolve eq8838 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq8838
  have eq8952 : (σ (M.op x y)) = (k (σ x) (σ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8845 eq770
    | exact resolve eq770 eq8845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq8845
  have eq8980 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq233 eq8952
    | exact resolve eq8952 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq8952
  have eq9086 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ y)))))) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq8980 eq997
    | exact resolve eq997 eq8980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq9093 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ (σ y))))))) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq8980 eq1439
    | exact resolve eq1439 eq8980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq11091 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8778 eq179
    | exact resolve eq179 eq8778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8778
  have eq11278 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11091 eq26
    | (have j1 := eq11091 (σ y)
       grind)
    | exact resolve eq26 eq11091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11091
  have eq11347 : x = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5276 eq11278
    | exact resolve eq11278 eq5276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5276 eq11278
  have eq11354 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq443
       have i₂ := eq11347
       grind)
    | exact superpose eq11347 eq443
    | exact resolve eq443 eq11347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq11347
  have eq11360 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq11354
  have eq11374 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq179 x x x
       have i₂ := eq11360
       grind)
    | exact superpose eq11360 eq179
    | exact resolve eq179 eq11360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11360
  have eq11456 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11374 y
       grind)
    | exact superpose eq11374 eq18
    | (have j1 := eq11374 y
       grind)
    | exact resolve eq18 eq11374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11374
  have eq11505 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq11456
  have eq11583 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11505 eq5636
    | (have r₁ := eq5636
       have r₂ := eq11505
       grind)
    | exact resolve eq5636 eq11505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5636 eq11505
  have eq11602 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq11583
  have eq11603 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq11602
  have eq11703 : ∀ X0 : G, (τ (σ x)) = (M.op (τ (σ x)) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11603 eq1869
    | exact resolve eq1869 eq11603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11603
  have eq11738 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq11703
    | exact resolve eq11703 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11703
  have eq13120 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11738 y
       grind)
    | exact superpose eq11738 eq18
    | (have j1 := eq11738 y
       grind)
    | exact resolve eq18 eq11738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11738
  have eq13169 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq13120
  have eq13193 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq13169
       grind)
    | exact superpose eq13169 eq18
    | exact resolve eq18 eq13169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq17296 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k (k X0 x) (σ (σ (σ (σ (σ y))))))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq9093 eq58
    | exact resolve eq58 eq9093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq9093
  have eq17350 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k (k X0 (M.op x y)) (σ (σ (σ (σ (σ y))))))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq13169 eq17296
    | exact resolve eq17296 eq13169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17296
  have eq17371 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (σ (σ (σ (σ (σ y))))))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq211 eq17350
    | exact resolve eq17350 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq17350
  have eq17384 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq9086 eq17371
    | exact resolve eq17371 eq9086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9086 eq17371
  have eq17390 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq17384 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq17384
    | exact resolve eq17384 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17384
  have eq17436 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq17390 eq477
    | (have j0 := eq477 (σ x)
       grind)
    | (have r₁ := eq477 (σ x)
       have r₂ := eq17390 (σ x)
       grind)
    | exact resolve eq477 eq17390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17390
  have eq17470 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq17436
  have eq17594 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq17470 eq179
    | exact resolve eq179 eq17470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17470
  have eq17671 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq17594 eq26
    | (have j1 := eq17594 (σ y)
       grind)
    | exact resolve eq26 eq17594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17594
  have eq17823 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq17671 eq8980
    | exact resolve eq8980 eq17671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8980 eq17671
  have eq17824 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq17823
  have eq17882 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq17824 eq31
    | exact resolve eq31 eq17824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq17824
  have eq18014 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq17882
    | exact resolve eq17882 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17882
  have eq18031 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13169 eq18014
    | exact resolve eq18014 eq13169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13169 eq18014
  have eq18032 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq18031
  have eq18092 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18032 eq1107
    | exact resolve eq1107 eq18032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18237 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18092 eq26
    | (have j1 := eq18092 (σ y)
       grind)
    | exact resolve eq26 eq18092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18092
  have eq18329 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18237 eq27
    | exact resolve eq27 eq18237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18237
  have eq18422 : y = (M.op x y) := by
    first
    | (have r₁ := eq18329
       have r₂ := eq18032
       grind)
    | exact resolve eq18329 eq18032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18032 eq18329
  have eq18450 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq18422
       grind)
    | exact superpose eq18422 eq24
    | exact resolve eq24 eq18422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq18451 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq18422
       grind)
    | exact superpose eq18422 eq36
    | exact resolve eq36 eq18422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq18457 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq431
       have i₂ := eq18422
       grind)
    | exact superpose eq18422 eq431
    | (have r₁ := eq431
       have r₂ := eq18422
       grind)
    | exact resolve eq431 eq18422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq18422
  have eq18485 : x = (k (M.op x y) x) ∨ x = (M.op x x) := by grind
  clear eq18457
  have eq18492 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18450 eq20
    | exact resolve eq20 eq18450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18680 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq18492 eq1107
    | exact resolve eq1107 eq18492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq21215 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18485 eq18451
    | exact resolve eq18451 eq18485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18451 eq18485
  have eq21231 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21215
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21215
    | exact resolve eq21215 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21215
  have eq21247 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21231 eq447
    | exact resolve eq447 eq21231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq21231
  have eq30337 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq21247 eq1662
    | exact resolve eq1662 eq21247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662 eq21247
  have eq30368 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq30337
    | exact resolve eq30337 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30337
  have eq30377 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq30368 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq30368 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq30368 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30368
  have eq30398 : x ≠ x ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq477 x
       have i₂ := eq30377 x
       grind)
    | exact superpose eq30377 eq477
    | (have j0 := eq477 x
       grind)
    | (have r₁ := eq477 x
       have r₂ := eq30377 x
       grind)
    | exact resolve eq477 eq30377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq30377
  have eq30436 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30398
  have eq30492 : ∀ X0 : G, x = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq179 x x x
       have i₂ := eq30436
       grind)
    | exact superpose eq30436 eq179
    | exact resolve eq179 eq30436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq30436
  have eq30753 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13193
       have i₂ := eq30492 sF0
       grind)
    | exact superpose eq30492 eq13193
    | (have j1 := eq30492 y
       grind)
    | exact resolve eq13193 eq30492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30492
  have eq30802 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30753
  have eq30829 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30802 eq27
    | exact resolve eq27 eq30802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30802
  have eq30924 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30829
       have r₂ := eq18492
       grind)
    | exact resolve eq30829 eq18492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18492 eq30829
  have eq30976 : ∀ X0 : G, (τ (σ x)) = (M.op (τ (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30924 eq1869
    | exact resolve eq1869 eq30924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869 eq30924
  have eq31010 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq30976
    | exact resolve eq30976 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq30976
  have eq31242 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13193
       have i₂ := eq31010 sF0
       grind)
    | exact superpose eq31010 eq13193
    | (have j1 := eq31010 y
       grind)
    | exact resolve eq13193 eq31010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13193 eq31010
  have eq31291 : x = (M.op x y) := by grind
  clear eq31242
  have eq31322 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq31291
       grind)
    | exact superpose eq31291 eq22
    | exact resolve eq22 eq31291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31291
  have eq31380 : (σ x) = (σ y) := by
    first
    | exact superpose eq31322 eq18450
    | exact resolve eq18450 eq31322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18450
  have eq31381 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31322 eq20
    | exact resolve eq20 eq31322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq31322
  have eq31572 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31380 eq26
    | exact resolve eq26 eq31380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31678 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq31380 eq18680
    | exact resolve eq18680 eq31380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18680 eq31380
  have eq31717 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31678 eq31572
    | (have j1 := eq31678 (σ y)
       grind)
    | exact resolve eq31572 eq31678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31572 eq31678
  have eq31855 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq31717 eq27
    | exact resolve eq27 eq31717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq31717
  have eq31944 : False := by grind
  exact eq31944

/-- `Equation3973`: `x ◇ y = (y ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pxy_Equation3973 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3973 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3973.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op X2 X0)) X2) := by
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : ∀ X0 : G, (M.op y X0) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X3 (M.op X0 X1)) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 (M.op X1 (M.op X2 X0))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op (M.op X3 X2) X0))) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op X1 (M.op (M.op X3 X2) X0)) X3
       have i₂ := eq16 X0 X1 (M.op X3 X2)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op y (M.op X1 (M.op (M.op x y) X0))) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (M.op X1 (M.op sF0 X0))
       have i₂ := eq16 X0 X1 sF0
       grind)
    | exact superpose eq16 eq174
    | exact resolve eq174 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op X1 (M.op y X0)) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) X0) y) x) = (M.op y (M.op (M.op X0 (M.op x y)) x)) := by
    intro X0
    first
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) y) = (M.op (M.op (M.op X0 X1) x) X1) := by
    intro X0 X1
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op x y) X0)) X2) = (M.op (M.op X2 (M.op (M.op X0 X1) x)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq537 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) X0) y) x) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq174 eq534
    | exact resolve eq534 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq960 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq976 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq980 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq985 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq986 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq985 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq988 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq960 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq990 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq988 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq988 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq988 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq991 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq986 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq986
    | (have j0 := eq986 (σ X0)
       grind)
    | exact resolve eq986 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq993 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq990 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq990
    | (have j0 := eq990 (σ X0) X1
       grind)
    | exact resolve eq990 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1851 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op (M.op X0 X1) x)) y) = (M.op (M.op (M.op (M.op (M.op x y) X0) y) x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq535 (M.op (M.op X0 X1) x) X1
       have i₂ := eq535 X0 X1
       grind)
    | (have i₁ := eq535 (M.op (M.op x y) X0) y
       have i₂ := eq535 X0 X1
       grind)
    | exact superpose eq535 eq535
    | exact resolve eq535 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq1874 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op (M.op X0 X1) x)) y) = (M.op (M.op y (M.op y X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq537 eq1851
    | exact resolve eq1851 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq1851
  have eq1876 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op x y) X0)) (M.op x y)) = (M.op (M.op y (M.op y X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1874 x y
       have i₂ := eq536 x sF0 y
       grind)
    | (have i₁ := eq1874 X0 X1
       have i₂ := eq536 X0 X1 sF0
       grind)
    | exact superpose eq536 eq1874
    | exact resolve eq1874 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq1874
  have eq1877 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y (M.op y X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1876 X0 X1
       have i₂ := eq16 X0 X1 sF0
       grind)
    | exact superpose eq16 eq1876
    | exact resolve eq1876 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq1930 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op X0 X2) (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X2) (M.op X1 (M.op X2 X3)) X3
       have i₂ := eq176 X2 X3 X0 X1
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1931 : ∀ X0 X1 X2 : G, (M.op x (M.op X1 (M.op X2 y))) = (M.op (M.op X0 X1) (M.op (M.op X0 X2) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 (M.op X0 X2) (M.op X1 (M.op X2 y))
       have i₂ := eq176 X2 y X0 X1
       grind)
    | exact superpose eq176 eq179
    | exact resolve eq179 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2089 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq179 X0 y
       have i₂ := eq1877 X0 (M.op X0 sF0)
       grind)
    | exact superpose eq1877 eq179
    | exact resolve eq179 eq1877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2090 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 y X0 X1 y
       have i₂ := eq1877 X0 (M.op X0 (M.op X1 y))
       grind)
    | exact superpose eq1877 eq176
    | exact resolve eq176 eq1877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2102 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X1) = (M.op X2 (M.op y (M.op y X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op y (M.op y X0)) X1
       have i₂ := eq1877 X0 (M.op X1 X2)
       grind)
    | exact superpose eq1877 eq16
    | exact resolve eq16 eq1877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2105 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) (M.op X1 (M.op x y))) = (M.op x (M.op y (M.op y X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X1 (M.op y (M.op y X0))
       have i₂ := eq1877 X0 (M.op y X1)
       grind)
    | exact superpose eq1877 eq179
    | exact resolve eq179 eq1877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2110 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op y (M.op y (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq174 (M.op y (M.op y X0))
       have i₂ := eq1877 X0 sF0
       grind)
    | exact superpose eq1877 eq174
    | exact resolve eq174 eq1877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq2114 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq174 eq2110
    | exact resolve eq2110 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq2110
  have eq2118 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op y (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq179 eq2105
    | exact resolve eq2105 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105
  have eq2120 : ∀ X0 X2 : G, (M.op X2 X0) = (M.op X2 (M.op y (M.op y X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq2102 X0 x X2
       have i₂ := eq16 X2 X0 x
       grind)
    | exact superpose eq16 eq2102
    | exact resolve eq2102 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102
  have eq2128 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2089 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2089
    | (have j0 := eq2089 X0
       grind)
    | exact resolve eq2089 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089
  have eq2149 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq2128 eq176
    | exact resolve eq176 eq2128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2155 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op (M.op x y) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2128 eq177
    | exact resolve eq177 eq2128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2128
  have eq2170 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2155 X0 X1 x
       have i₂ := eq1930 X0 X1 sF0 x
       grind)
    | exact superpose eq1930 eq2155
    | exact resolve eq2155 eq1930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930 eq2155
  have eq2227 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2090 X0 (M.op X1 (M.op y X0))
       have i₂ := eq16 X0 X1 y
       grind)
    | exact superpose eq16 eq2090
    | exact resolve eq2090 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090
  have eq2337 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) (M.op (M.op y X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq179 (M.op y X0) y
       have i₂ := eq2114 X0
       grind)
    | exact superpose eq2114 eq179
    | exact resolve eq179 eq2114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2114
  have eq2350 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq1931 eq2337
    | exact resolve eq2337 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931 eq2337
  have eq2355 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq2350 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2350
    | (have j0 := eq2350 X0
       grind)
    | exact resolve eq2350 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq2375 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op X0 y) x X0
       have i₂ := eq2355 X0
       grind)
    | exact superpose eq2355 eq16
    | exact resolve eq16 eq2355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2355
  have eq2468 : ∀ X0 : G, (M.op x x) = (M.op (M.op x X0) (M.op (M.op y X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq179 (M.op y X0) x
       have i₂ := eq2118 X0
       grind)
    | exact superpose eq2118 eq179
    | exact resolve eq179 eq2118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118
  have eq2485 : ∀ X0 : G, (M.op x x) = (M.op (M.op x X0) (M.op (M.op (M.op x y) X0) y)) := by
    intro X0
    first
    | (have i₁ := eq2468 x
       have i₂ := eq2170 y x sF0
       grind)
    | (have i₁ := eq2468 x
       have i₂ := eq2170 sF0 x y
       grind)
    | exact superpose eq2170 eq2468
    | exact resolve eq2468 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2468
  have eq2506 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X0 X1) (M.op (M.op y X1) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq179 (M.op y X1) X0
       have i₂ := eq2120 X1 X0
       grind)
    | exact superpose eq2120 eq179
    | exact resolve eq179 eq2120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq2120
  have eq2548 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2506 X0 X1
       have i₂ := eq2170 y X1 sF0
       grind)
    | (have i₁ := eq2506 X0 X1
       have i₂ := eq2170 sF0 X1 y
       grind)
    | exact superpose eq2170 eq2506
    | exact resolve eq2506 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2506
  have eq3093 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq976
       grind)
    | exact superpose eq976 eq40
    | exact resolve eq40 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq976
  have eq3094 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3093
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3093
    | exact resolve eq3093 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3093
  have eq3096 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq3094
    | exact resolve eq3094 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3094
  have eq4479 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X1 x) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2170 X1 x (M.op X0 y)
       have i₂ := eq2375 X0
       grind)
    | (have i₁ := eq2170 X0 X0 (M.op x y)
       have i₂ := eq2375 X0
       grind)
    | exact superpose eq2375 eq2170
    | exact resolve eq2170 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq135543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3096 eq980
    | exact resolve eq980 eq3096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980 eq3096
  have eq135551 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq135543
       have r₂ := eq27
       grind)
    | exact resolve eq135543 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135543
  have eq135742 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq135551 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq135551
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq135551
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq135551
       grind)
    | exact resolve eq13 eq135551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135796 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq135742 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135742
  have eq136290 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq135796 eq135551
    | exact resolve eq135551 eq135796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135551 eq135796
  have eq136321 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq136290
  have eq136678 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq136321 eq152
    | exact resolve eq152 eq136321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq136321
  have eq136689 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31 eq136678
    | exact resolve eq136678 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq136678
  have eq136694 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq986 (σ x)
       grind)
    | (have r₁ := eq136689
       have r₂ := eq986 y
       grind)
    | exact resolve eq136689 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136689
  have eq136721 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq136694 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq136694
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq136694
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq136694
       grind)
    | exact resolve eq13 eq136694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136775 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq136721 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136721
  have eq138489 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq136775 eq136694
    | exact resolve eq136694 eq136775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136694 eq136775
  have eq138525 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq138489
  have eq138864 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq138525 eq141
    | exact resolve eq141 eq138525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq138525
  have eq138875 : x = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq138864
    | exact resolve eq138864 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq138864
  have eq138880 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq986 y
       grind)
    | (have r₁ := eq138875
       have r₂ := eq986 x
       grind)
    | exact resolve eq138875 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986 eq138875
  have eq138941 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq138880
       grind)
    | exact superpose eq138880 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq138880
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq138880
       grind)
    | exact resolve eq13 eq138880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138995 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq138941 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138941
  have eq139466 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq138995 x
       grind)
    | exact superpose eq138995 eq18
    | (have j1 := eq138995 x
       grind)
    | exact resolve eq18 eq138995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139481 : y = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq138880
       have i₂ := eq138995 y
       grind)
    | exact superpose eq138995 eq138880
    | exact resolve eq138880 eq138995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138880 eq138995
  have eq139588 : y = (k y y) ∨ x = (M.op x x) := by grind
  clear eq139481
  have eq140030 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq139466
       grind)
    | exact superpose eq139466 eq39
    | exact resolve eq39 eq139466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq139466
  have eq140033 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq140030
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq140030
    | exact resolve eq140030 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140030
  have eq140037 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq140033
    | exact resolve eq140033 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140033
  have eq140043 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq993 y X0
       have i₂ := eq139588
       grind)
    | exact superpose eq139588 eq993
    | (have j0 := eq993 y X0
       grind)
    | exact resolve eq993 eq139588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139588
  have eq140052 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq140043 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140043
  have eq140054 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq140052 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq140052
    | (have j0 := eq140052 X0
       grind)
    | exact resolve eq140052 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140052
  have eq142058 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq140054 eq26
    | (have j1 := eq140054 (σ x)
       grind)
    | exact resolve eq26 eq140054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140054
  have eq142140 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq140037 eq142058
    | exact resolve eq142058 eq140037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140037 eq142058
  have eq142332 : x = (M.op x x) := by
    first
    | (have r₁ := eq142140
       have r₂ := eq27
       grind)
    | exact resolve eq142140 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142140
  have eq142463 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) x) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq4479 X0 x
       have i₂ := eq142332
       grind)
    | exact superpose eq142332 eq4479
    | exact resolve eq4479 eq142332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4479
  have eq142471 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq142332
       grind)
    | exact superpose eq142332 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq142332
       grind)
    | exact resolve eq13 eq142332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142489 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq2227 x x x
       have i₂ := eq142332
       grind)
    | exact superpose eq142332 eq2227
    | exact resolve eq2227 eq142332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227
  have eq142525 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq142471 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142471
  have eq142553 : ∀ X0 : G, (M.op x (M.op X0 y)) = (k x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq142463 X0
       have i₂ := eq142525 (M.op sF0 X0)
       grind)
    | exact superpose eq142525 eq142463
    | exact resolve eq142463 eq142525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142463
  have eq142732 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op (M.op (M.op x y) (M.op X0 x)) y)) := by
    intro X0
    first
    | (have i₁ := eq2548 X0 (M.op X0 x)
       have i₂ := eq142489 X0
       grind)
    | exact superpose eq142489 eq2548
    | exact resolve eq2548 eq142489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2548
  have eq142801 : (M.op x x) = (M.op x (M.op (M.op (M.op x y) (M.op x x)) y)) := by
    first
    | (have i₁ := eq2485 (M.op x x)
       have i₂ := eq142489 x
       grind)
    | exact superpose eq142489 eq2485
    | exact resolve eq2485 eq142489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485 eq142489
  have eq142938 : (M.op x x) = (k x (M.op (M.op x y) (M.op (M.op x y) (M.op x x)))) := by
    first
    | (have i₁ := eq142801
       have i₂ := eq142553 (M.op sF0 (M.op x x))
       grind)
    | exact superpose eq142553 eq142801
    | exact resolve eq142801 eq142553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142801
  have eq142984 : ∀ X0 : G, (M.op x X0) = (k x (M.op (M.op x y) (M.op (M.op x y) (M.op X0 x)))) := by
    intro X0
    first
    | (have i₁ := eq142732 X0
       have i₂ := eq142553 (M.op sF0 (M.op X0 x))
       grind)
    | exact superpose eq142553 eq142732
    | exact resolve eq142732 eq142553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142553 eq142732
  have eq143075 : (M.op x x) = (k x (M.op x x)) := by
    first
    | exact superpose eq2149 eq142938
    | exact resolve eq142938 eq2149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142938
  have eq143104 : ∀ X0 : G, (M.op x X0) = (k x (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq2149 eq142984
    | exact resolve eq142984 eq2149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149 eq142984
  have eq143167 : x = (k x x) := by
    first
    | (have i₁ := eq143075
       have i₂ := eq142332
       grind)
    | exact superpose eq142332 eq143075
    | exact resolve eq143075 eq142332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142332 eq143075
  have eq143186 : ∀ X0 : G, (k x (k x X0)) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq143104 X0
       have i₂ := eq142525 X0
       grind)
    | exact superpose eq142525 eq143104
    | exact resolve eq143104 eq142525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142525 eq143104
  have eq146714 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq993 x X0
       have i₂ := eq143167
       grind)
    | exact superpose eq143167 eq993
    | (have j0 := eq993 x X0
       grind)
    | exact resolve eq993 eq143167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq146715 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq991 x
       have i₂ := eq143167
       grind)
    | exact superpose eq143167 eq991
    | (have j0 := eq991 x
       grind)
    | exact resolve eq991 eq143167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991 eq143167
  have eq146722 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq146715
  have eq146723 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq146714 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146714
  have eq146724 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq146722
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq146722
    | exact resolve eq146722 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146722
  have eq146725 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq146723 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq146723
    | (have j0 := eq146723 X0
       grind)
    | exact resolve eq146723 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq146723
  have eq146774 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq146724 eq2170
    | exact resolve eq2170 eq146724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170 eq146724
  have eq146840 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq146725 eq146774
    | exact resolve eq146774 eq146725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146774
  have eq146894 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) (k (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq146725 eq146840
    | exact resolve eq146840 eq146725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146725 eq146840
  have eq153363 : ∀ X0 : G, (k (σ x) (σ (k x X0))) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq35 (k x X0)
       have i₂ := eq143186 X0
       grind)
    | exact superpose eq143186 eq35
    | exact resolve eq35 eq143186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143186
  have eq153373 : ∀ X0 : G, (k (σ x) (k (σ x) (σ X0))) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq153363 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq153363
    | exact resolve eq153363 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq153363
  have eq153379 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq146894 eq153373
    | exact resolve eq153373 eq146894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146894 eq153373
  have eq155391 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq153379 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq153379
    | (have j0 := eq153379 y
       grind)
    | exact resolve eq153379 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq153379
  have eq155569 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq155391
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq155391
    | exact resolve eq155391 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq155391
  have eq155631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq155569
    | exact resolve eq155569 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq155569
  have eq155654 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq155631
    | exact resolve eq155631 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq155631
  have eq155669 : False := by grind
  exact eq155669

/-- `Equation3973`: `x ◇ y = (y ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pyx_Equation3973 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3973 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3973.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op X2 X0)) X2) := by
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  clear eq24 eq35
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
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  clear eq36
  have eq87 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq87 y x
       grind)
    | exact superpose eq87 eq69
    | (have j1 := eq87 x x
       grind)
    | exact resolve eq69 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq216 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq111 eq87
    | (have j0 := eq87 x (σ x)
       grind)
    | exact resolve eq87 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq574 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq573
    | exact resolve eq573 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq577 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq574
       have r₂ := eq27
       grind)
    | exact resolve eq574 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq639 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq577 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq577
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq577
       grind)
    | exact resolve eq13 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq639 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq651 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq644 eq49
    | exact resolve eq49 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq644
  have eq667 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq577 eq651
    | exact resolve eq651 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq651
  have eq680 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by grind
  clear eq667
  have eq682 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq680
    | exact resolve eq680 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq680
  have eq685 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq87 x x
       have i₂ := eq682
       grind)
    | exact superpose eq682 eq87
    | (have j0 := eq87 x x
       grind)
    | exact resolve eq87 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq686 : x = (M.op x x) := by grind
  clear eq685
  have eq705 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq686
       grind)
    | exact superpose eq686 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq686
       grind)
    | exact resolve eq13 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 x
       have i₂ := eq686
       grind)
    | exact superpose eq686 eq14
    | exact resolve eq14 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq705 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq712 : ∀ X0 : G, (M.op (τ X0) x) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq710 (τ X0)
       have i₂ := eq216 X0
       grind)
    | exact superpose eq216 eq710
    | exact resolve eq710 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq719 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq710 x
       grind)
    | exact superpose eq710 eq43
    | exact resolve eq43 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq724 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq719
       have i₂ := eq686
       grind)
    | exact superpose eq686 eq719
    | exact resolve eq719 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq719
  have eq726 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq724
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq724
    | exact resolve eq724 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq724
  have eq752 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq726 eq87
    | (have j0 := eq87 x (σ x)
       grind)
    | exact resolve eq87 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq726
  have eq753 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq752
  have eq759 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq753 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq753
       grind)
    | exact resolve eq13 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq753 eq14
    | exact resolve eq14 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq764 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq759 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq939 : ∀ X0 : G, (M.op (τ X0) x) = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq764 eq712
    | exact resolve eq712 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq954 : (τ (M.op (k (σ x) (σ y)) (σ x))) = (M.op (k x y) x) := by
    first
    | exact superpose eq57 eq939
    | exact resolve eq939 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq939
  have eq971 : (M.op (M.op y x) x) = (τ (M.op (k (σ x) (σ y)) (σ x))) := by
    first
    | (have i₁ := eq954
       have i₂ := eq710 y
       grind)
    | exact superpose eq710 eq954
    | exact resolve eq954 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq954
  have eq977 : (M.op (M.op y x) x) = (τ (M.op (M.op (σ y) (σ x)) (σ x))) := by
    first
    | exact superpose eq764 eq971
    | exact resolve eq971 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq971
  have eq981 : (M.op x y) = (τ (M.op (M.op (σ y) (σ x)) (σ x))) := by
    first
    | (have i₁ := eq977
       have i₂ := eq709 y
       grind)
    | exact superpose eq709 eq977
    | exact resolve eq977 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq977
  have eq983 : (M.op x y) = (τ (M.op (M.op (σ y) (σ x)) (σ x))) := by
    first
    | (have i₁ := eq981
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq981
    | exact resolve eq981 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq981
  have eq986 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ x)) (σ x)) := by
    first
    | exact superpose eq983 eq15
    | exact resolve eq15 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq1003 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ x)) (σ x)) := by
    first
    | exact superpose eq20 eq986
    | exact resolve eq986 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq986
  have eq1086 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq763 eq1003
    | exact resolve eq1003 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763 eq1003
  have eq1094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1086
    | exact resolve eq1086 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1086
  have eq1096 : False := by grind
  exact eq1096

/-- `Equation3973`: `x ◇ y = (y ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pyx_x_pyx_Equation3973 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3973 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3973.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op X2 X0)) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X3 (M.op X0 X1)) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X1 (M.op X2 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op (M.op X3 X2) X0))) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op (M.op X3 X2) X0)) X3
       have i₂ := eq9 X0 X1 (M.op X3 X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X1 (M.op X3 X4))) = (M.op (M.op X0 X1) (M.op (M.op X0 X3) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 X4 (M.op X0 X3) X2 (M.op X1 (M.op X3 X4))
       have i₂ := eq62 X3 X4 X0 X1
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op X0 X2) (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X2) (M.op X1 (M.op X2 X3)) X3
       have i₂ := eq62 X2 X3 X0 X1
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 (M.op X0 X2)) X4) X1) = (M.op (M.op X2 X3) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 (M.op X3 (M.op X0 X2)) X4 (M.op X2 X3) X1
       have i₂ := eq62 X2 X3 X0 X1
       grind)
    | exact superpose eq62 eq63
    | exact resolve eq63 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq195 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1 (M.op X0 X1) X2
       have i₂ := eq77 X2 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq77 eq62
    | exact resolve eq62 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq243 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X0
       have i₂ := eq195 X2 (M.op X0 X1) X0
       grind)
    | (have i₁ := eq9 X1 X2 X0
       have i₂ := eq195 X0 (M.op X0 X1) X2
       grind)
    | exact superpose eq195 eq9
    | exact resolve eq9 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X2 X0 X1 X3
       have i₂ := eq195 X3 (M.op X2 X0) (M.op X0 (M.op X1 X2))
       grind)
    | (have i₁ := eq62 X2 X0 X1 X3
       have i₂ := eq195 (M.op X0 (M.op X1 X2)) (M.op X2 X0) X3
       grind)
    | exact superpose eq195 eq62
    | exact resolve eq62 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq266 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op X2 X0) (M.op (M.op X2 X0) (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq244 X0 X1 X2 X3
       have i₂ := eq88 X1 X3 X2 X0 (M.op X2 X0)
       grind)
    | exact superpose eq88 eq244
    | exact resolve eq244 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq244
  have eq286 : ∀ X0 X1 X3 : G, (M.op X1 X3) = (M.op X1 (M.op X0 (M.op X0 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq266 X0 X1 x X3
       have i₂ := eq71 x X0 X1 X0 X3
       grind)
    | exact superpose eq71 eq266
    | exact resolve eq266 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq266
  have eq308 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X2 X0 X1 X2
       have i₂ := eq243 X2 X0 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq243 eq62
    | exact resolve eq62 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq243
  have eq454 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq308 X2 X0 (M.op X0 X1)
       have i₂ := eq286 X0 X2 X1
       grind)
    | exact superpose eq286 eq308
    | exact resolve eq308 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3482 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) X0) ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X1 X2) X0) ∨ (M.op X1 X2) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq308 (M.op X1 X2) X1 X2
       have i₂ := eq14 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq308 X0 X1 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq14 eq308
    | (have j1 := eq14 (M.op X1 X2) X0
       grind)
    | exact resolve eq308 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq3506 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) X0) ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3482 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3482
  have eq3529 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3506 X0 X1 X2
       have j1 := eq12 (M.op X1 X2) X0
       grind)
    | (have r₁ := eq3506 X1 X1 X2
       have r₂ := eq12 (M.op X1 X2) X1
       grind)
    | exact resolve eq3506 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3506
  have eq3608 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3529 X0 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq3529 X0 X1 X2
       have i₂ := eq14 X0 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq3529
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq3529 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3621 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3608 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq3608 X1 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq3608 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3608
  have eq4516 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3621 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621
  have eq4517 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4516 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4516
  have eq4541 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4517 (σ X0)
       grind)
    | exact superpose eq4517 eq15
    | exact resolve eq15 eq4517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4544 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k X0 (τ (σ X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X0) X1
       have i₂ := eq4517 (σ X0)
       grind)
    | exact superpose eq4517 eq28
    | exact resolve eq28 eq4517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4561 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4544 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4544
    | exact resolve eq4544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4544
  have eq4564 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4541 X0
       have i₂ := eq4517 X0
       grind)
    | exact superpose eq4517 eq4541
    | exact resolve eq4541 eq4517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4541
  have eq4580 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4561 X0 X1
       have i₂ := eq4517 X0
       grind)
    | exact superpose eq4517 eq4561
    | exact resolve eq4561 eq4517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4517 eq4561
  have eq4594 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4580 X0 X1
       have i₂ := eq3529 X1 X0 X0
       grind)
    | exact superpose eq3529 eq4580
    | exact resolve eq4580 eq3529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4580
  have eq4603 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (σ X0) (σ X0))) = (σ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4594 X0 X1
       have i₂ := eq3529 (σ X1) (σ X0) (σ X0)
       grind)
    | exact superpose eq3529 eq4594
    | exact resolve eq4594 eq3529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4594
  have eq4607 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4603 X0 X1
       have i₂ := eq4564 X0
       grind)
    | exact superpose eq4564 eq4603
    | exact resolve eq4603 eq4564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4603
  have eq4719 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq454 X1 (σ X0) (σ X0)
       have i₂ := eq4564 X0
       grind)
    | exact superpose eq4564 eq454
    | exact resolve eq454 eq4564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq4564
  have eq4744 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4719 X0 X1
       have i₂ := eq4607 X0 X0
       grind)
    | exact superpose eq4607 eq4719
    | exact resolve eq4719 eq4607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4607 eq4719
  have eq5320 : ∀ X0 X1 X2 : G, (σ (k (M.op X1 (M.op X1 X1)) X2)) = (k (M.op X0 (M.op X0 (σ X1))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (M.op X1 (M.op X1 X1)) X2
       have i₂ := eq4744 X1 X0
       grind)
    | exact superpose eq4744 eq15
    | exact resolve eq15 eq4744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4744
  have eq5347 : ∀ X0 X1 X2 : G, (σ (k (M.op X1 (M.op X1 X1)) X2)) = (M.op (σ X2) (M.op X0 (M.op X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5320 X0 X1 X2
       have i₂ := eq3529 (σ X2) X0 (M.op X0 (σ X1))
       grind)
    | exact superpose eq3529 eq5320
    | exact resolve eq5320 eq3529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5320
  have eq5444 : ∀ X1 X2 : G, (σ (k (M.op X1 (M.op X1 X1)) X2)) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq5347 x X1 X2
       have i₂ := eq286 x (σ X2) (σ X1)
       grind)
    | (have i₁ := eq5347 x X1 X2
       have i₂ := eq286 x (σ X2) (M.op x (M.op x (σ X1)))
       grind)
    | exact superpose eq286 eq5347
    | exact resolve eq5347 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5347
  have eq5497 : ∀ X1 X2 : G, (M.op (σ X2) (σ X1)) = (σ (M.op X2 (M.op X1 (M.op X1 X1)))) := by
    intro X1 X2
    first
    | (have i₁ := eq5444 X1 X2
       have i₂ := eq3529 X2 X1 (M.op X1 X1)
       grind)
    | exact superpose eq3529 eq5444
    | exact resolve eq5444 eq3529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3529 eq5444
  have eq5523 : ∀ X1 X2 : G, (M.op (σ X2) (σ X1)) = (σ (M.op X2 X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq5497 X1 X2
       have i₂ := eq286 X1 X2 X1
       grind)
    | (have i₁ := eq5497 X1 X1
       have i₂ := eq286 x X1 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq286 eq5497
    | exact resolve eq5497 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq5497
  have eq5703 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5523 y x
       grind)
    | exact superpose eq5523 eq16
    | (have r₁ := eq16
       have r₂ := eq5523 y x
       grind)
    | exact resolve eq16 eq5523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5523
  have eq5755 : False := by grind
  exact eq5755

/-- `Equation3997`: `x ◇ y = (z ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pyx_pxx_pyx_Equation3997 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3997 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3997.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X0 X2)) X1) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 (M.op X0 X1)) X2) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq47 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 X1 X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq38
    | (have j0 := eq38 X0 X1 X2
       grind)
    | exact resolve eq38 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq151 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq157 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1
       have j1 := eq47 X0 X1 x
       grind)
    | (have r₁ := eq151 X1 X0
       have r₂ := eq47 X0 X1 X1
       grind)
    | (have r₁ := eq151 X0 X1
       have r₂ := eq47 X0 X1 X0
       grind)
    | (have r₁ := eq151 X1 X1
       have r₂ := eq47 (M.op X1 X1) X1 x
       grind)
    | exact resolve eq151 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq151
  have eq1235 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq157
  have eq1254 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1235 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1856 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1254 (σ X1) (σ X0)
       grind)
    | exact superpose eq1254 eq15
    | exact resolve eq15 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1869 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1856 X0 X1
       have i₂ := eq1254 X1 X0
       grind)
    | exact superpose eq1254 eq1856
    | exact resolve eq1856 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254 eq1856
  have eq1881 : False := by grind
  exact eq1881

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_pyx_x_pxy_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
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
  clear eq35
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) x X2
       have i₂ := eq16 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq36
    | exact resolve eq36 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq181 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq37 (M.op sF0 sF0)
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq37
    | exact resolve eq37 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq182 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq181
    | exact resolve eq181 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq183 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq180
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq180
    | exact resolve eq180 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq192 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq203 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq29 eq192
    | exact resolve eq192 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq210 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq221 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq31 eq210
    | exact resolve eq210 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq210
  have eq730 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1
       have i₂ := eq176 X0 X2
       grind)
    | (have i₁ := eq176 X0 X2
       have i₂ := eq176 X0 (M.op X0 X0)
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq782 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq783 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq808 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1736 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq782
       grind)
    | exact superpose eq782 eq39
    | exact resolve eq39 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1737 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1736
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1736
    | exact resolve eq1736 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq1739 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1737
    | exact resolve eq1737 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737
  have eq4908 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq791 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq791
    | (have j0 := eq791 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq791 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq791 X0 X0
       have r₂ := eq11 X0 (k X0 X0)
       grind)
    | exact resolve eq791 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq4916 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4908 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq4908 (M.op X1 X1) X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq4908 (M.op X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq4908 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq4908 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4908
  have eq16561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1739 eq783
    | exact resolve eq783 eq1739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16568 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16561
       have r₂ := eq27
       grind)
    | exact resolve eq16561 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16561
  have eq16577 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16568 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16568
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16568
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq16568
       grind)
    | exact resolve eq12 eq16568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16568
  have eq16579 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq16577
  have eq16581 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16579
       have r₂ := eq26
       grind)
    | exact resolve eq16579 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16579
  have eq16584 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1739 eq16581
    | exact resolve eq16581 eq1739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739 eq16581
  have eq16586 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16584
       have r₂ := eq27
       grind)
    | exact resolve eq16584 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16584
  have eq16588 : y = (k y (τ (σ x))) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16586 eq221
    | exact resolve eq221 eq16586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16586
  have eq16606 : y = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq16588
    | exact resolve eq16588 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16588
  have eq16608 : (M.op x y) = (M.op y x) ∨ y = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq16606
       have r₂ := eq13 y x
       grind)
    | exact resolve eq16606 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16606
  have eq16612 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq16608
       grind)
    | exact superpose eq16608 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq16608
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq16608
       grind)
    | exact resolve eq12 eq16608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16608
  have eq16614 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq16612
       have r₂ := eq13 y x
       grind)
    | exact resolve eq16612 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16612
  have eq16617 : (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq16614
       have r₂ := eq18
       grind)
    | exact resolve eq16614 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16614
  have eq16622 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq16617
       grind)
    | exact superpose eq16617 eq39
    | exact resolve eq39 eq16617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16617
  have eq16624 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16622
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16622
    | exact resolve eq16622 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16622
  have eq16628 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | exact superpose eq20 eq16624
    | exact resolve eq16624 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16624
  have eq16633 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq16628 eq783
    | exact resolve eq783 eq16628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16640 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq16633
       have r₂ := eq27
       grind)
    | exact resolve eq16633 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16633
  have eq16735 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq16640 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16640
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16640
       grind)
    | exact resolve eq12 eq16640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16640
  have eq16737 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq16735
  have eq16739 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq16737
       have r₂ := eq26
       grind)
    | exact resolve eq16737 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16737
  have eq16742 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq16628 eq16739
    | exact resolve eq16739 eq16628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16628 eq16739
  have eq16744 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq16742
       have r₂ := eq27
       grind)
    | exact resolve eq16742 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16742
  have eq16750 : y = (k y (τ (σ x))) ∨ y = (k y x) := by
    first
    | exact superpose eq16744 eq221
    | exact resolve eq221 eq16744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq16744
  have eq16768 : y = (k y x) ∨ y = (k y x) := by
    first
    | exact superpose eq29 eq16750
    | exact resolve eq16750 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16750
  have eq16769 : y = (k y x) := by grind
  clear eq16768
  have eq16777 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq782
       have i₂ := eq16769
       grind)
    | exact superpose eq16769 eq782
    | exact resolve eq782 eq16769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq16779 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq16769
       grind)
    | exact superpose eq16769 eq39
    | exact resolve eq39 eq16769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16780 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16779
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16779
    | exact resolve eq16779 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16779
  have eq16792 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq16780 eq783
    | exact resolve eq783 eq16780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq17520 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq16777
       grind)
    | exact superpose eq16777 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq16777
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq16777
       grind)
    | exact resolve eq12 eq16777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16777
  have eq17522 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq17520
  have eq17524 : x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17522
       have r₂ := eq18
       grind)
    | exact resolve eq17522 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17522
  have eq17527 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17524
       have i₂ := eq16769
       grind)
    | exact superpose eq16769 eq17524
    | exact resolve eq17524 eq16769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16769 eq17524
  have eq17528 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq17527
  have eq17530 : x = (k y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17528
       have i₂ := eq808 y
       grind)
    | exact superpose eq808 eq17528
    | (have j1 := eq808 y
       grind)
    | exact resolve eq17528 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17533 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq17528
       grind)
    | exact superpose eq17528 eq16
    | exact resolve eq16 eq17528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17538 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq730 y X1 x
       have i₂ := eq17528
       grind)
    | exact superpose eq17528 eq730
    | exact resolve eq730 eq17528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17547 : x ≠ x ∨ x = y ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq17528
       grind)
    | exact superpose eq17528 eq12
    | exact resolve eq12 eq17528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17548 : x = (k y y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq17547
  have eq17551 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17548 eq17530
    | exact resolve eq17530 eq17548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17530
  have eq17552 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17533 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17533
    | (have j0 := eq17533 y X0
       grind)
    | exact resolve eq17533 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17533
  have eq17607 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq17552 sF0
       have i₂ := eq808 sF0
       grind)
    | exact superpose eq808 eq17552
    | (have j1 := eq808 (M.op x y)
       grind)
    | exact resolve eq17552 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17621 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17552 eq808
    | exact resolve eq808 eq17552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17552
  have eq17667 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq17538 X0 x
       have i₂ := eq808 x
       grind)
    | exact superpose eq808 eq17538
    | (have j1 := eq808 x
       grind)
    | exact resolve eq17538 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17698 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq17538 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq17538 X0 y
       grind)
    | exact superpose eq17538 eq18
    | (have j1 := eq17538 y X0
       grind)
    | exact resolve eq18 eq17538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17538
  have eq17754 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17698 eq17667
    | (have j0 := eq17667 y
       grind)
    | exact resolve eq17667 eq17698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17667
  have eq17766 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17698 eq17754
    | exact resolve eq17754 eq17698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17754
  have eq17785 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17698 x
       have i₂ := eq808 x
       grind)
    | exact superpose eq808 eq17698
    | (have j1 := eq808 x
       grind)
    | exact resolve eq17698 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17796 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ x = (k x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq17698 x
       grind)
    | exact superpose eq17698 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq17698 x
       grind)
    | exact resolve eq13 eq17698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17834 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq17766 eq17785
    | exact resolve eq17785 eq17766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17785
  have eq17883 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq17548
       grind)
    | exact superpose eq17548 eq40
    | exact resolve eq40 eq17548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17548
  have eq17888 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17883
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17883
    | exact resolve eq17883 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17883
  have eq17892 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17888
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17888
    | exact resolve eq17888 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17888
  have eq17942 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq17766
       grind)
    | exact superpose eq17766 eq39
    | exact resolve eq39 eq17766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17766
  have eq17948 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17942
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17942
    | exact resolve eq17942 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17942
  have eq17952 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq17948
    | exact resolve eq17948 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17948
  have eq18044 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq16792 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16792
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16792
       grind)
    | exact resolve eq12 eq16792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16792
  have eq18046 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18044
  have eq18048 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18046
       have r₂ := eq26
       grind)
    | exact resolve eq18046 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18046
  have eq18051 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16780 eq18048
    | exact resolve eq18048 eq16780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18048
  have eq18052 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18051
  have eq18056 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ y) = (k (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18052 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18052
       grind)
    | exact resolve eq13 eq18052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18062 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq18052 eq730
    | exact resolve eq730 eq18052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18071 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18052 eq12
    | exact resolve eq12 eq18052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18052
  have eq18072 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18071
  have eq18392 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18062 eq26
    | (have j1 := eq18062 (σ y) X0
       grind)
    | exact resolve eq26 eq18062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18062
  have eq18492 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18392 eq174
    | exact resolve eq174 eq18392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18502 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18392 eq808
    | exact resolve eq808 eq18392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18392
  have eq18586 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18072 eq115
    | exact resolve eq115 eq18072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq18601 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq18586
    | exact resolve eq18586 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18586
  have eq18799 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq17551
       grind)
    | exact superpose eq17551 eq40
    | exact resolve eq40 eq17551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq17551
  have eq18806 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18799
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18799
    | exact resolve eq18799 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18799
  have eq18810 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18806
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18806
    | exact resolve eq18806 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18806
  have eq18814 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17698 eq18810
    | exact resolve eq18810 eq17698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17698 eq18810
  have eq19119 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq17607 eq174
    | exact resolve eq174 eq17607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17607
  have eq19857 : x ≠ x ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4916 y y
       have i₂ := eq18601
       grind)
    | exact superpose eq18601 eq4916
    | (have j0 := eq4916 y y
       grind)
    | exact resolve eq4916 eq18601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18601
  have eq19885 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq17892 eq4916
    | (have j0 := eq4916 (σ y) (σ y)
       grind)
    | exact resolve eq4916 eq17892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19889 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18814 eq4916
    | (have j0 := eq4916 (σ y) (σ y)
       grind)
    | exact resolve eq4916 eq18814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4916
  have eq19905 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19889
  have eq19906 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19905
  have eq19913 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq19885
  have eq19914 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq19913
  have eq19952 : x ≠ x ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19857
  have eq19953 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19952
  have eq20069 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19906 eq19914
    | exact resolve eq19914 eq19906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19906 eq19914
  have eq20070 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20069
  have eq20077 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17528 eq19953
    | exact resolve eq19953 eq17528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17528 eq19953
  have eq20186 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20070 eq174
    | exact resolve eq174 eq20070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq20200 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20070
  have eq20269 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq19119
  have eq20277 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20269
       have r₂ := eq17621
       grind)
    | exact resolve eq20269 eq17621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17621 eq20269
  have eq20289 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20277 eq41
    | exact resolve eq41 eq20277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq20295 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20277 eq841
    | (have j0 := eq841 (M.op x y)
       grind)
    | exact resolve eq841 eq20277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq20277
  have eq20303 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq20289
    | exact resolve eq20289 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20289
  have eq20307 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20303
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20303
    | exact resolve eq20303 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20303
  have eq20655 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20186 eq17892
    | exact resolve eq17892 eq20186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17892
  have eq20659 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20186 eq18814
    | exact resolve eq18814 eq20186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18814 eq20186
  have eq20676 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq20659
  have eq20678 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq20655
  have eq20687 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20676
       have r₂ := eq20200
       grind)
    | exact resolve eq20676 eq20200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20676
  have eq20689 : x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq20678
       have r₂ := eq20200
       grind)
    | exact resolve eq20678 eq20200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20200 eq20678
  have eq20702 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20687 eq20689
    | exact resolve eq20689 eq20687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20687 eq20689
  have eq20703 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20702
  have eq20719 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq20703 eq730
    | exact resolve eq730 eq20703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20703
  have eq20904 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20719 eq26
    | (have j1 := eq20719 (σ y) X0
       grind)
    | exact resolve eq26 eq20719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20719
  have eq21021 : x = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20904 eq203
    | exact resolve eq203 eq20904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq21049 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20904 eq808
    | exact resolve eq808 eq20904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20904
  have eq21687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21049 eq17952
    | exact resolve eq17952 eq21049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17952
  have eq21710 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21687
  have eq21724 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21710
       have r₂ := eq27
       grind)
    | exact resolve eq21710 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21710
  have eq21748 : x = (k x (τ (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21724 eq21021
    | exact resolve eq21021 eq21724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21021 eq21724
  have eq21753 : x = (k x (τ (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq21748
  have eq21760 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq21753
    | exact resolve eq21753 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21753
  have eq21766 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq17796 x
       grind)
    | (have r₁ := eq21760
       have r₂ := eq17796 y
       grind)
    | (have r₁ := eq21760
       have r₂ := eq17796 x
       grind)
    | exact resolve eq21760 eq17796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17796 eq21760
  have eq21783 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17834
       have i₂ := eq21766
       grind)
    | exact superpose eq21766 eq17834
    | exact resolve eq17834 eq21766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17834
  have eq21788 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq21766
       grind)
    | exact superpose eq21766 eq39
    | exact resolve eq39 eq21766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21766
  have eq21803 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq21783
  have eq21815 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21788
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21788
    | exact resolve eq21788 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21788
  have eq21818 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21803
       have r₂ := eq20295
       grind)
    | exact resolve eq21803 eq20295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20295 eq21803
  have eq22033 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21815 eq21049
    | exact resolve eq21049 eq21815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21049 eq21815
  have eq22049 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22033
  have eq22068 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22049 eq27
    | exact resolve eq27 eq22049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22049
  have eq22103 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21818 eq182
    | exact resolve eq182 eq21818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq21818
  have eq22143 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq22103
    | exact resolve eq22103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22103
  have eq22150 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20307 eq22143
    | exact resolve eq22143 eq20307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20307 eq22143
  have eq22153 : y = (M.op x y) := by
    first
    | (have r₁ := eq22150
       have r₂ := eq22068
       grind)
    | exact resolve eq22150 eq22068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22068 eq22150
  have eq22154 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22153
       grind)
    | exact superpose eq22153 eq18
    | exact resolve eq18 eq22153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq22155 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq22153
       grind)
    | exact superpose eq22153 eq24
    | exact resolve eq24 eq22153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq22158 : (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq183
       have i₂ := eq22153
       grind)
    | exact superpose eq22153 eq183
    | exact resolve eq183 eq22153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq22209 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22155 eq20
    | exact resolve eq20 eq22155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22212 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq22155 eq15
    | exact resolve eq15 eq22155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39283 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20077 eq22158
    | exact resolve eq22158 eq20077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20077 eq22158
  have eq39348 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq39283
    | exact resolve eq39283 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39283
  have eq39362 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22209 eq39348
    | exact resolve eq39348 eq22209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39348
  have eq39370 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq18056 (σ y)
       grind)
    | (have r₁ := eq39362
       have r₂ := eq18056 (σ y)
       grind)
    | exact resolve eq39362 eq18056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18056 eq39362
  have eq39377 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39370
       have i₂ := eq22153
       grind)
    | exact superpose eq22153 eq39370
    | exact resolve eq39370 eq22153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22153 eq39370
  have eq39402 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39377 eq18072
    | exact resolve eq18072 eq39377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18072 eq39377
  have eq39439 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq39402
  have eq39520 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq39439 eq730
    | exact resolve eq730 eq39439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq39439
  have eq39911 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq39520 X0 x
       have i₂ := eq808 x
       grind)
    | exact superpose eq808 eq39520
    | (have j1 := eq808 x
       grind)
    | exact resolve eq39520 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq40001 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq22154
       have i₂ := eq39520 sF0 x
       grind)
    | (have i₁ := eq22154
       have i₂ := eq39520 X0 sF0
       grind)
    | exact superpose eq39520 eq22154
    | (have j1 := eq39520 y X0
       grind)
    | exact resolve eq22154 eq39520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22154 eq39520
  have eq40101 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40001 eq39911
    | (have j0 := eq39911 y
       grind)
    | exact resolve eq39911 eq40001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39911
  have eq40137 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40001 eq40101
    | exact resolve eq40101 eq40001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40001 eq40101
  have eq41593 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq40137
       grind)
    | exact superpose eq40137 eq39
    | exact resolve eq39 eq40137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq40137
  have eq41625 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41593
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq41593
    | exact resolve eq41593 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41593
  have eq41631 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq41625
    | exact resolve eq41625 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41625
  have eq41635 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22209 eq41631
    | exact resolve eq41631 eq22209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41631
  have eq41667 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41635 eq18502
    | exact resolve eq18502 eq41635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18502
  have eq41709 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq41667
  have eq41745 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41709 eq27
    | exact resolve eq27 eq41709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41709
  have eq41763 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq41745
       have r₂ := eq22209
       grind)
    | exact resolve eq41745 eq22209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22209 eq41745
  have eq41775 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41763 eq18492
    | exact resolve eq18492 eq41763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18492
  have eq41793 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq41775
  have eq42000 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41793 eq41635
    | exact resolve eq41635 eq41793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41635 eq41793
  have eq42018 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq42000
  have eq42032 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41763 eq42018
    | exact resolve eq42018 eq41763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41763 eq42018
  have eq42033 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq42032
  have eq42154 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42033 eq22212
    | exact resolve eq22212 eq42033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22212 eq42033
  have eq42212 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq42154
    | exact resolve eq42154 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq42154
  have eq42213 : x = (M.op x y) := by grind
  clear eq42212
  have eq42290 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq42213
       grind)
    | exact superpose eq42213 eq22
    | exact resolve eq22 eq42213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq42213
  have eq42466 : (σ x) = (σ y) := by
    first
    | exact superpose eq42290 eq22155
    | exact resolve eq22155 eq42290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22155
  have eq42467 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq42290 eq20
    | exact resolve eq20 eq42290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq42290
  have eq42907 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq42466 eq26
    | exact resolve eq26 eq42466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq42976 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq42466 eq16780
    | exact resolve eq16780 eq42466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16780 eq42466
  have eq44022 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq42907 eq12
    | exact resolve eq12 eq42907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42907
  have eq44023 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq44022
  have eq44026 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42976 eq44023
    | exact resolve eq44023 eq42976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42976 eq44023
  have eq44027 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq44026
  have eq44062 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq44027 eq27
    | exact resolve eq27 eq44027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq44027
  have eq44089 : False := by grind
  exact eq44089
