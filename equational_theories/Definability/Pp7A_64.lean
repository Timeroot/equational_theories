import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxx_pyy_pxy_Equation3506 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X3)) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq27 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 x (M.op (M.op x x) x)
       have i₂ := eq9 X0 (M.op x (M.op (M.op x x) x)) x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x x x
       have i₂ := eq9 X1 x x x
       grind)
    | (have i₁ := eq9 X0 (M.op (M.op x x) x) x x
       have i₂ := eq9 (M.op (M.op x x) x) X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X4 X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq27 X4 x X3
       have i₂ := eq27 X1 x X0
       grind)
    | (have i₁ := eq27 X0 (M.op X0 X0) x
       have i₂ := eq27 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq27 eq27
    | exact resolve eq27 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X0 (M.op X1 X1)) = X2 ∨ (M.op X0 (M.op X1 X1)) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq27 X0 X1 X2
       grind)
    | (have i₁ := eq13 X2 (M.op X0 X0)
       have i₂ := eq27 X0 X1 X2
       grind)
    | exact superpose eq27 eq13
    | (have r₁ := eq13 X2 (M.op X0 X0)
       have r₂ := eq27 X0 (M.op X0 X0) X2
       grind)
    | (have r₁ := eq13 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq27 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq28 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq98 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (k X2 X2) ∨ (M.op X0 (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq88 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq94 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq94 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq94 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq103 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq99 (σ X0)
       grind)
    | exact superpose eq99 eq15
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq103 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq103
    | exact resolve eq103 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq119 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq127 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X2) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq138 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq143 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq119 X0 X1
       have i₂ := eq106 X1
       grind)
    | exact superpose eq106 eq119
    | (have j0 := eq119 X0 X1
       grind)
    | exact resolve eq119 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq147 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X1
       have i₂ := eq106 X1
       grind)
    | exact superpose eq106 eq143
    | (have j0 := eq143 X0 X1
       grind)
    | exact resolve eq143 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq428 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (σ X0)
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq28
    | exact resolve eq28 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq428 (σ X0) X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq428
    | exact resolve eq428 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1005 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq27 X3 x X2
       have i₂ := eq611 X0 x
       grind)
    | exact superpose eq611 eq27
    | exact resolve eq27 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq611
  have eq1162 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq138 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq138
    | (have j0 := eq138 (σ X1) X1
       grind)
    | exact resolve eq138 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq138 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq1230 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1227 X0 X1
       have j1 := eq127 X0 X1 x
       grind)
    | (have r₁ := eq1227 x x
       have r₂ := eq127 x x x
       grind)
    | (have r₁ := eq1227 X0 X1
       have r₂ := eq127 X0 X1 X1
       grind)
    | exact resolve eq1227 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq1227
  have eq1241 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1162 X0 X1
       have i₂ := eq106 X1
       grind)
    | exact superpose eq106 eq1162
    | (have j0 := eq1162 X0 X1
       grind)
    | exact resolve eq1162 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1247 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1241 X0 X1
       have i₂ := eq106 X1
       grind)
    | exact superpose eq106 eq1241
    | (have j0 := eq1241 X0 X1
       grind)
    | exact resolve eq1241 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq4102 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq147 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq4108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4102 X0 X1
       have j1 := eq1247 X0 X1
       grind)
    | (have r₁ := eq4102 X0 X1
       have r₂ := eq1247 X0 X1
       grind)
    | exact resolve eq4102 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247 eq4102
  have eq8114 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq8118 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8114 X0 X1
       have i₂ := eq99 X1
       grind)
    | exact superpose eq99 eq8114
    | (have j0 := eq8114 X0 X1
       grind)
    | exact resolve eq8114 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8114
  have eq8336 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8118 X2 X1
       have i₂ := eq28 X1 X0
       grind)
    | (have i₁ := eq8118 X2 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq8118
    | (have j0 := eq8118 X2 X1
       grind)
    | (have r₁ := eq8118 X0 (M.op X1 X1)
       have r₂ := eq28 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq8118 X0 (M.op X0 X0)
       have r₂ := eq28 X0 (M.op X0 X0)
       grind)
    | exact resolve eq8118 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq8458 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1230 (τ X0) X1
       grind)
    | exact superpose eq1230 eq17
    | (have j1 := eq1230 X0 X1
       grind)
    | exact resolve eq17 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1230
  have eq8633 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq8336 X0 (k X1 X1) X0
       grind)
    | (have r₁ := eq8336 X0 (k X0 X0) x
       have r₂ := eq99 X0
       grind)
    | exact resolve eq8336 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8336
  have eq9426 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X2 (M.op x x) x
       have i₂ := eq8633 (M.op x x) X0
       grind)
    | exact superpose eq8633 eq53
    | exact resolve eq53 eq8633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq9438 : ∀ X0 X1 : G, (k X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X1
       have i₂ := eq8633 (σ X1) X0
       grind)
    | exact superpose eq8633 eq106
    | exact resolve eq106 eq8633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq8633
  have eq21707 : ∀ X0 X1 X2 : G, (k X2 X2) ≠ X2 ∨ (M.op X0 (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq98 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq21710 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ X2 ∨ (M.op X0 (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21707 X0 X1 X2
       have i₂ := eq99 X2
       grind)
    | exact superpose eq99 eq21707
    | (have j0 := eq21707 X0 X1 X2
       grind)
    | exact resolve eq21707 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq21707
  have eq46823 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq4108 X1 X0
       grind)
    | exact superpose eq4108 eq10
    | (have j1 := eq4108 X1 X0
       grind)
    | exact resolve eq10 eq4108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4108
  have eq46854 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46823 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46823
    | (have j0 := eq46823 X0 X1
       grind)
    | exact resolve eq46823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46823
  have eq1992391 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8458 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8458
    | (have j0 := eq8458 X0 X1
       grind)
    | exact resolve eq8458 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8458
  have eq1997095 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1992391 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1992391
    | (have j0 := eq1992391 X0 X1
       grind)
    | exact resolve eq1992391 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992391
  have eq2096343 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46854 y x
       grind)
    | exact superpose eq46854 eq16
    | (have j1 := eq46854 y x
       grind)
    | exact resolve eq16 eq46854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46854
  have eq2098717 : y = (M.op y y) := by
    first
    | (have j1 := eq1997095 x y
       grind)
    | (have r₁ := eq2096343
       have r₂ := eq1997095 x y
       grind)
    | exact resolve eq2096343 eq1997095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997095 eq2096343
  have eq2099494 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq428 y X0
       have i₂ := eq2098717
       grind)
    | exact superpose eq2098717 eq428
    | exact resolve eq428 eq2098717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq2099551 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (σ (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1005 y X0 X1
       have i₂ := eq2098717
       grind)
    | exact superpose eq2098717 eq1005
    | exact resolve eq1005 eq2098717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq2099818 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq8118 X0 y
       have i₂ := eq2098717
       grind)
    | exact superpose eq2098717 eq8118
    | (have j0 := eq8118 X0 y
       grind)
    | (have r₁ := eq8118 X0 y
       have r₂ := eq2098717
       grind)
    | exact resolve eq8118 eq2098717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8118
  have eq2099843 : ∀ X0 X1 : G, (k X1 X1) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq9426 X1 X0 y
       have i₂ := eq2098717
       grind)
    | exact superpose eq2098717 eq9426
    | exact resolve eq9426 eq2098717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9426
  have eq2099845 : ∀ X0 : G, (σ y) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9438 X0 y
       have i₂ := eq2098717
       grind)
    | exact superpose eq2098717 eq9438
    | exact resolve eq9438 eq2098717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9438
  have eq2099940 : ∀ X0 X1 : G, y ≠ y ∨ y = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21710 X0 X1 y
       have i₂ := eq2098717
       grind)
    | exact superpose eq2098717 eq21710
    | (have j0 := eq21710 X0 X1 y
       grind)
    | (have r₁ := eq21710 X0 X1 y
       have r₂ := eq2098717
       grind)
    | exact resolve eq21710 eq2098717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21710 eq2098717
  have eq2100330 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2099940 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099940
  have eq2100331 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq2099818 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099818
  have eq2100365 : ∀ X0 : G, (σ y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq2099843 X0 x
       have i₂ := eq2099845 x
       grind)
    | exact superpose eq2099845 eq2099843
    | exact resolve eq2099843 eq2099845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099843 eq2099845
  have eq2100598 : y = (σ (σ y)) := by
    first
    | (have i₁ := eq2099551 x x
       have i₂ := eq2100330 x x
       grind)
    | exact superpose eq2100330 eq2099551
    | exact resolve eq2099551 eq2100330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099551 eq2100330
  have eq2100624 : y = (σ y) := by
    first
    | (have i₁ := eq2099494 x
       have i₂ := eq2100331 x
       grind)
    | exact superpose eq2100331 eq2099494
    | exact resolve eq2099494 eq2100331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099494 eq2100331
  have eq2113599 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2100624
       grind)
    | exact superpose eq2100624 eq16
    | exact resolve eq16 eq2100624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2113762 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq2113599
       have i₂ := eq2100365 (σ x)
       grind)
    | exact superpose eq2100365 eq2113599
    | exact resolve eq2113599 eq2100365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113599
  have eq2113812 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2113762
       have i₂ := eq2100624
       grind)
    | exact superpose eq2100624 eq2113762
    | exact resolve eq2113762 eq2100624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100624 eq2113762
  have eq2113851 : y ≠ (σ (σ y)) := by
    first
    | (have i₁ := eq2113812
       have i₂ := eq2100365 x
       grind)
    | exact superpose eq2100365 eq2113812
    | exact resolve eq2113812 eq2100365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100365 eq2113812
  have eq2113881 : False := by grind
  exact eq2113881

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pxy_y_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq43 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
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
  have eq51 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq61 : ∀ X0 : G, (σ (k X0 (k x (M.op x y)))) = (k (σ X0) (k (σ x) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq46 eq10
    | exact resolve eq10 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq25 eq37
  have eq82 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X0 (M.op X1 X1)) X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq45
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq45 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq103 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq82 y y
       grind)
    | exact superpose eq82 eq75
    | (have j1 := eq82 y y
       grind)
    | exact resolve eq75 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq111
    | exact resolve eq111 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq87
       have i₂ := eq82 sF3 sF3
       grind)
    | exact superpose eq82 eq87
    | (have j1 := eq82 (σ y) (σ y)
       grind)
    | exact resolve eq87 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38
    | exact resolve eq38 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq206 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq204
    | exact resolve eq204 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq231 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq251 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ x = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq82 x (τ X0)
       grind)
    | exact superpose eq82 eq43
    | (have j1 := eq82 x (τ X0)
       grind)
    | exact resolve eq43 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq332 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq355 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X1) X3) ∨ (M.op X0 X1) = (k X0 (M.op (M.op X2 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X2 (M.op (M.op X3 X1) X0)
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq13
    | (have r₁ := eq13 (M.op X3 X1) (M.op (M.op X3 X1) X1)
       have r₂ := eq55 X1 X1 (M.op X3 X1) X3
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : (k x (k (M.op x y) (M.op x y))) = (τ (k (σ x) (k (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq160 eq254
    | exact resolve eq254 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 : G, (M.op x (τ X0)) = (τ (k (σ x) X0)) ∨ x = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq254 X0
       have i₂ := eq82 x (τ X0)
       grind)
    | exact superpose eq82 eq254
    | (have j1 := eq82 x (τ X0)
       grind)
    | exact resolve eq254 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq529 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq231 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq231
    | exact resolve eq231 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq231 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq231
    | (have j0 := eq231 X0 x
       grind)
    | exact resolve eq231 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq21 eq231
    | (have j0 := eq231 X0 (M.op x y)
       grind)
    | exact resolve eq231 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq622 : ∀ X0 : G, (τ (k X0 (σ (M.op x y)))) = (M.op (τ X0) (M.op x y)) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq546 X0
       have i₂ := eq82 (τ X0) sF0
       grind)
    | exact superpose eq82 eq546
    | (have j1 := eq82 (τ X0) (M.op x y)
       grind)
    | exact resolve eq546 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq645 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq332 X0 X1
       have i₂ := eq82 (σ X0) X1
       grind)
    | exact superpose eq82 eq332
    | (have j1 := eq82 (σ X0) X1
       grind)
    | exact resolve eq332 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq675 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq112 eq82
    | (have j0 := eq82 (σ x) (σ y)
       grind)
    | exact resolve eq82 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq675
    | exact resolve eq675 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq679 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq676
       have r₂ := eq28
       grind)
    | exact resolve eq676 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq683 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq679 eq13
    | exact resolve eq13 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4528 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq355 (M.op X0 X1) X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq42569 : (M.op (M.op x y) y) = (k (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq4528 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4528
    | (have j0 := eq4528 x y
       grind)
    | exact resolve eq4528 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43587 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq645 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq645
    | exact resolve eq645 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq43872 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43587 X0 X1
       have i₂ := eq529 X1 X0
       grind)
    | exact superpose eq529 eq43587
    | (have j0 := eq43587 X0 X1
       grind)
    | exact resolve eq43587 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529 eq43587
  have eq1088260 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq679 eq113
    | exact resolve eq113 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq679
  have eq1088774 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq1088260
    | exact resolve eq1088260 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088260
  have eq1088777 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq1088774
       grind)
    | exact superpose eq1088774 eq75
    | exact resolve eq75 eq1088774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088774
  have eq1088942 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1088777
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1088777
    | exact resolve eq1088777 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088777
  have eq1088984 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1088942
       have r₂ := eq683
       grind)
    | exact resolve eq1088942 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq1088942
  have eq1089080 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1088984 eq87
    | exact resolve eq87 eq1088984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088984
  have eq1089298 : x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq1089080
    | exact resolve eq1089080 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089080
  have eq1089378 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82 y y
       have i₂ := eq1089298
       grind)
    | exact superpose eq1089298 eq82
    | (have j0 := eq82 x y
       grind)
    | exact resolve eq82 eq1089298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1089404 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq1089378
  have eq1090160 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1089404
       grind)
    | exact superpose eq1089404 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1089404
       grind)
    | exact resolve eq13 eq1089404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090170 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq1089404
  have eq1090171 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq1090160
  have eq1090823 : x = y ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1089298
       have i₂ := eq1090171
       grind)
    | exact superpose eq1090171 eq1089298
    | exact resolve eq1089298 eq1090171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089298 eq1090171
  have eq1090886 : x = y ∨ x = (M.op y y) := by grind
  clear eq1090823
  have eq1090939 : x = (M.op y y) := by
    first
    | (have r₁ := eq1090886
       have r₂ := eq1090170
       grind)
    | exact resolve eq1090886 eq1090170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090170 eq1090886
  have eq1091058 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq103
       have i₂ := eq1090939
       grind)
    | exact superpose eq1090939 eq103
    | exact resolve eq103 eq1090939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq1091082 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1090939
       grind)
    | exact superpose eq1090939 eq13
    | exact resolve eq13 eq1090939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091083 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq1090939
       grind)
    | exact superpose eq1090939 eq14
    | exact resolve eq14 eq1090939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091084 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 y X0 y
       have i₂ := eq1090939
       grind)
    | exact superpose eq1090939 eq55
    | exact resolve eq55 eq1090939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091089 : (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq4528 y y
       have i₂ := eq1090939
       grind)
    | exact superpose eq1090939 eq4528
    | exact resolve eq4528 eq1090939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091096 : (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq1091089
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1091089
    | exact resolve eq1091089 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091089
  have eq1091104 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1091058
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1091058
    | exact resolve eq1091058 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091058
  have eq1091633 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1091096 eq46
    | exact resolve eq46 eq1091096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091857 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq1091633
    | exact resolve eq1091633 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091633
  have eq1091974 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1091857
       have i₂ := eq82 sF2 sF1
       grind)
    | exact superpose eq82 eq1091857
    | (have j1 := eq82 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq1091857 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1093052 : (τ (σ x)) = (k y y) ∨ x = y := by
    first
    | exact superpose eq1091104 eq87
    | exact resolve eq87 eq1091104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq1091104
  have eq1093200 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq29 eq1093052
    | exact resolve eq1093052 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093052
  have eq1093204 : x = (k y y) := by
    first
    | (have r₁ := eq1093200
       have r₂ := eq1091082
       grind)
    | exact resolve eq1093200 eq1091082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091082 eq1093200
  have eq1093208 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq1093204
       grind)
    | exact superpose eq1093204 eq75
    | exact resolve eq75 eq1093204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1093204
  have eq1093363 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1093208
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1093208
    | exact resolve eq1093208 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093208
  have eq1093512 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1093363
       have i₂ := eq82 sF3 sF3
       grind)
    | exact superpose eq82 eq1093363
    | (have j1 := eq82 (σ y) (σ y)
       grind)
    | exact resolve eq1093363 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1094441 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1091083 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1091083
    | (have j0 := eq1091083 y
       grind)
    | exact resolve eq1091083 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1094804 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1094441
       have i₂ := eq1090939
       grind)
    | exact superpose eq1090939 eq1094441
    | exact resolve eq1094441 eq1090939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090939 eq1094441
  have eq1094833 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1094804 eq14
    | exact resolve eq14 eq1094804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094804
  have eq1094848 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1094833 X0
       have i₂ := eq1091083 X0
       grind)
    | exact superpose eq1091083 eq1094833
    | exact resolve eq1094833 eq1091083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091083 eq1094833
  have eq1094875 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (k X0 (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq1094848 eq13
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq1094848 x
       grind)
    | exact resolve eq13 eq1094848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1096312 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1091974 eq13
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq1091974
       grind)
    | exact resolve eq13 eq1091974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1096319 : (M.op (σ x) (σ (M.op x y))) = (k (σ x) (M.op (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1091974 eq4528
    | exact resolve eq4528 eq1091974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1096984 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1093512 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1093512
       grind)
    | exact resolve eq13 eq1093512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1096994 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1093512
  have eq1096995 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1096984
  have eq1096996 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1093363 eq1096995
    | exact resolve eq1096995 eq1093363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093363 eq1096995
  have eq1096998 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq1096996
       have r₂ := eq1096994
       grind)
    | exact resolve eq1096996 eq1096994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096994 eq1096996
  have eq1097034 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1096998 eq14
    | exact resolve eq14 eq1096998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1097035 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1096998 eq55
    | exact resolve eq55 eq1096998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1097040 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1096998 eq4528
    | exact resolve eq4528 eq1096998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4528 eq1096998
  have eq1097045 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq1097040
    | exact resolve eq1097040 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097040
  have eq1113832 : ∀ X0 : G, (τ (σ (k X0 (k x (M.op x y))))) = (τ (M.op (σ X0) (k (σ x) (σ (M.op x y))))) ∨ (σ X0) = (M.op (k (σ x) (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq61 eq43872
    | (have j0 := eq43872 (σ X0) (k (σ x) (σ (M.op x y)))
       grind)
    | exact resolve eq43872 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq43872
  have eq1117097 : ∀ X0 : G, (τ (M.op (σ X0) (σ (M.op x y)))) = (τ (σ (k X0 (k x (M.op x y))))) ∨ (σ X0) = (M.op (k (σ x) (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1091857 eq1113832
    | (have j0 := eq1113832 X0
       grind)
    | exact resolve eq1113832 eq1091857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113832
  have eq1117712 : ∀ X0 : G, (k X0 (k x (M.op x y))) = (τ (M.op (σ X0) (σ (M.op x y)))) ∨ (σ X0) = (M.op (k (σ x) (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq1117097 X0
       have i₂ := eq16 (k X0 (k x sF0))
       grind)
    | exact superpose eq16 eq1117097
    | (have j0 := eq1117097 X0
       grind)
    | exact resolve eq1117097 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117097
  have eq1118027 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (M.op (σ X0) (σ (M.op x y)))) ∨ (σ X0) = (M.op (k (σ x) (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1091096 eq1117712
    | (have j0 := eq1117712 X0
       grind)
    | exact resolve eq1117712 eq1091096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117712
  have eq1118142 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (M.op (σ X0) (σ (M.op x y)))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1091857 eq1118027
    | (have j0 := eq1118027 X0
       grind)
    | exact resolve eq1118027 eq1091857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118027
  have eq1125638 : ∀ X0 : G, (τ (k X0 (σ (M.op x y)))) = (M.op (τ X0) y) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1094848 eq622
    | (have j0 := eq622 X0
       grind)
    | exact resolve eq622 eq1094848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq1125639 : ∀ X0 : G, (τ (k X0 (σ (M.op x y)))) = (M.op (τ X0) y) ∨ (τ X0) = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq1094848 eq1125638
    | (have j0 := eq1125638 X0
       grind)
    | exact resolve eq1125638 eq1094848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094848 eq1125638
  have eq1126258 : (M.op (M.op x y) y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq31 eq1125639
    | (have j0 := eq1125639 (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq1125639 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1125639
  have eq1126363 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq160 eq1126258
    | exact resolve eq1126258 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126258
  have eq1126509 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | (have j1 := eq1094875 (M.op x y)
       grind)
    | (have r₁ := eq1126363
       have r₂ := eq1094875 (M.op x y)
       grind)
    | exact resolve eq1126363 eq1094875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094875 eq1126363
  have eq1126733 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq1126509 eq126
    | exact resolve eq126 eq1126509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq1126979 : (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) = (σ (k (M.op x y) (M.op (M.op x y) y))) := by
    first
    | exact superpose eq1126733 eq38
    | exact resolve eq38 eq1126733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1127259 : (σ (M.op (M.op x y) y)) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq42569 eq1126979
    | exact resolve eq1126979 eq42569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126979
  have eq1127286 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1126733 eq1127259
    | exact resolve eq1127259 eq1126733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127259
  have eq1127314 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1127286
       have i₂ := eq82 sF1 sF1
       grind)
    | exact superpose eq82 eq1127286
    | (have j1 := eq82 (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) (σ (M.op x y))
       grind)
    | exact resolve eq1127286 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127286
  have eq1144265 : (τ (k (σ x) (k (σ (M.op x y)) (σ (M.op x y))))) = (M.op x (k (M.op x y) (M.op x y))) ∨ x = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq160 eq458
    | exact resolve eq458 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1144351 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (τ (k (σ x) X0))) ∨ x = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1091084 X1 (τ X0)
       have i₂ := eq458 X0
       grind)
    | exact superpose eq458 eq1091084
    | (have j1 := eq458 X0
       grind)
    | exact resolve eq1091084 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq1144496 : (τ (k (σ x) (k (σ (M.op x y)) (σ (M.op x y))))) = (M.op x (M.op (M.op x y) y)) ∨ x = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq1126509 eq1144265
    | exact resolve eq1144265 eq1126509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144265
  have eq1144662 : (M.op x y) = (τ (k (σ x) (k (σ (M.op x y)) (σ (M.op x y))))) ∨ x = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq206 eq1144496
    | exact resolve eq1144496 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144496
  have eq1144748 : (M.op x y) = (k x (k (M.op x y) (M.op x y))) ∨ x = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq454 eq1144662
    | exact resolve eq1144662 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq1144662
  have eq1144826 : (M.op x y) = (k x (M.op (M.op x y) y)) ∨ x = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq1126509 eq1144748
    | exact resolve eq1144748 eq1126509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144748
  have eq1144869 : (M.op x y) = (k x (M.op (M.op x y) y)) ∨ x = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1144826
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1144826
    | exact resolve eq1144826 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144826
  have eq1144903 : x = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) ∨ (M.op x y) = (k x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq1126509 eq1144869
    | exact resolve eq1144869 eq1126509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144869
  have eq1144926 : (M.op x y) = (k x (M.op (M.op x y) y)) ∨ x = (M.op (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq206 eq1144903
    | exact resolve eq1144903 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144903
  have eq1185105 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1091974 eq1127314
    | exact resolve eq1127314 eq1091974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127314
  have eq1254232 : (k (k x (M.op x y)) (M.op x y)) = (τ (M.op (k (σ x) (σ (M.op x y))) (σ (M.op x y)))) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq46 eq1118142
    | exact resolve eq1118142 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq1118142
  have eq1255024 : (k (k x (M.op x y)) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1091857 eq1254232
    | exact resolve eq1254232 eq1091857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254232
  have eq1255233 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1091096 eq1255024
    | exact resolve eq1255024 eq1091096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091096 eq1255024
  have eq1255314 : (M.op (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1126509 eq1255233
    | exact resolve eq1255233 eq1126509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255233
  have eq1255374 : (M.op (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1091857 eq1255314
    | exact resolve eq1255314 eq1091857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091857 eq1255314
  have eq1255441 : (σ (k (M.op x y) (M.op (M.op x y) y))) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1255374 eq117
    | exact resolve eq117 eq1255374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq1255374
  have eq1256030 : (σ (M.op (M.op x y) y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq42569 eq1255441
    | exact resolve eq1255441 eq42569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42569 eq1255441
  have eq1256110 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1126733 eq1256030
    | exact resolve eq1256030 eq1126733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126733 eq1256030
  have eq1257730 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1091974 eq1256110
    | exact resolve eq1256110 eq1091974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091974 eq1256110
  have eq1291066 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1257730 eq1185105
    | exact resolve eq1185105 eq1257730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185105 eq1257730
  have eq1291101 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1291066
  have eq1291107 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1291101
       have r₂ := eq1096312
       grind)
    | exact resolve eq1291101 eq1096312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096312 eq1291101
  have eq1291143 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1291107 eq160
    | exact resolve eq160 eq1291107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq1291107
  have eq1291285 : (τ (σ x)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1126509 eq1291143
    | exact resolve eq1291143 eq1126509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126509 eq1291143
  have eq1291301 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq29 eq1291285
    | exact resolve eq1291285 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1291285
  have eq1291883 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq1291301 eq1097035
    | exact resolve eq1097035 eq1291301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097035
  have eq1293563 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq27 eq1291883
    | (have j0 := eq1291883 (σ x)
       grind)
    | exact resolve eq1291883 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291883
  have eq1294019 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) y) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1293563 eq1291301
    | exact resolve eq1291301 eq1293563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291301 eq1293563
  have eq1294058 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) y) := by grind
  clear eq1294019
  have eq1294069 : x = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq1294058
       have r₂ := eq28
       grind)
    | exact resolve eq1294058 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294058
  have eq1294184 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1294069 eq1144926
    | exact resolve eq1144926 eq1294069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144926
  have eq1294215 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq1294069 eq206
    | exact resolve eq206 eq1294069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq1294069
  have eq1294277 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1294184
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1294184
    | exact resolve eq1294184 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294184
  have eq1295385 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1294215 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1294215
    | (have j0 := eq1294215 x
       grind)
    | exact resolve eq1294215 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1296186 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq1295385
       grind)
    | exact superpose eq1295385 eq13
    | exact resolve eq13 eq1295385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1298581 : (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq1296186
       have r₂ := eq1294277
       grind)
    | exact resolve eq1296186 eq1294277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294277 eq1296186
  have eq1298583 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1298581
       grind)
    | exact superpose eq1298581 eq44
    | exact resolve eq44 eq1298581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1298581
  have eq1298768 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq1298583
    | exact resolve eq1298583 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298583
  have eq1298937 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1298768
       have i₂ := eq82 sF2 sF2
       grind)
    | exact superpose eq82 eq1298768
    | (have j1 := eq82 (σ x) (σ x)
       grind)
    | exact resolve eq1298768 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1312119 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1298937 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1298937
       grind)
    | exact resolve eq13 eq1298937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1312129 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1298937
  have eq1312130 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1312119
  have eq1312135 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1298768 eq1312130
    | exact resolve eq1312130 eq1298768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298768 eq1312130
  have eq1312655 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq1312135
       have r₂ := eq1312129
       grind)
    | exact resolve eq1312135 eq1312129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312129 eq1312135
  have eq1312681 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1312655 eq1097034
    | exact resolve eq1097034 eq1312655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097034
  have eq1312701 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq1312681
    | exact resolve eq1312681 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312681
  have eq2349079 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (τ (k (σ x) X0))) ∨ x = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1144351 X0 X1
       have i₂ := eq1294215 X1
       grind)
    | exact superpose eq1294215 eq1144351
    | (have j0 := eq1144351 X0 X1
       grind)
    | exact resolve eq1144351 eq1294215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144351
  have eq2349087 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (τ (M.op (σ x) (σ (M.op x y))))) ∨ x = (M.op (τ (M.op (σ x) (σ (M.op x y)))) (τ (M.op (σ x) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1096319 eq2349079
    | (have j0 := eq2349079 (M.op (σ x) (σ (M.op x y))) x
       grind)
    | exact resolve eq2349079 eq1096319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096319 eq2349079
  have eq2350077 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (τ (M.op (σ x) (σ y)))) ∨ x = (M.op (τ (M.op (σ x) (σ (M.op x y)))) (τ (M.op (σ x) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1312701 eq2349087
    | exact resolve eq2349087 eq1312701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349087
  have eq2350235 : ∀ X0 : G, x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op X0 x) = (M.op X0 (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1312701 eq2350077
    | (have j0 := eq2350077 X0
       grind)
    | exact resolve eq2350077 eq1312701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350077
  have eq2350311 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op X0 x) = (M.op X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1312701 eq2350235
    | (have j0 := eq2350235 X0
       grind)
    | exact resolve eq2350235 eq1312701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312701 eq2350235
  have eq2350331 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (τ (M.op (σ x) (σ y)))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq2350311 X0
       grind)
    | (have r₁ := eq2350311 X0
       have r₂ := eq28
       grind)
    | exact resolve eq2350311 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350311
  have eq2353649 : (σ (M.op x x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2350331 eq251
    | (have j0 := eq251 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq251 eq2350331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq2350331
  have eq2353755 : (σ (M.op x x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by grind
  clear eq2353649
  have eq2353769 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1097045 eq2353755
    | exact resolve eq2353755 eq1097045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097045 eq2353755
  have eq2353870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2353769
       have i₂ := eq1295385
       grind)
    | exact superpose eq1295385 eq2353769
    | exact resolve eq2353769 eq1295385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295385 eq2353769
  have eq2353937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq21 eq2353870
    | exact resolve eq2353870 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2353870
  have eq2353974 : x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have r₁ := eq2353937
       have r₂ := eq28
       grind)
    | exact resolve eq2353937 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353937
  have eq2354120 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq2353974 eq55
    | exact resolve eq55 eq2353974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq2354132 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2354120 X0 x
       have i₂ := eq1091084 X0 x
       grind)
    | exact superpose eq1091084 eq2354120
    | exact resolve eq2354120 eq1091084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091084 eq2354120
  have eq2354246 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2354132 X0
       have i₂ := eq1294215 X0
       grind)
    | exact superpose eq1294215 eq2354132
    | exact resolve eq2354132 eq1294215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294215 eq2354132
  have eq2354510 : x = (M.op (τ (M.op (σ x) (σ y))) x) := by
    first
    | exact superpose eq2353974 eq2354246
    | exact resolve eq2354246 eq2353974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353974 eq2354246
  have eq2355334 : x ≠ x ∨ x = (k (τ (M.op (σ x) (σ y))) x) := by
    first
    | exact superpose eq2354510 eq13
    | (have r₁ := eq13 (τ (M.op (σ x) (σ y))) x
       have r₂ := eq2354510
       grind)
    | exact resolve eq13 eq2354510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354510
  have eq2355346 : x = (k (τ (M.op (σ x) (σ y))) x) := by grind
  clear eq2355334
  have eq2355352 : x = (τ (k (M.op (σ x) (σ y)) (σ x))) := by
    first
    | (have i₁ := eq2355346
       have i₂ := eq544 sF4
       grind)
    | exact superpose eq544 eq2355346
    | exact resolve eq2355346 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq2355346
  have eq2355614 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq2355352 eq15
    | exact resolve eq15 eq2355352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2355352
  have eq2356495 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq2355614
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2355614
    | exact resolve eq2355614 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2355614
  have eq2356847 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2356495 eq82
    | (have j0 := eq82 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq82 eq2356495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq2356495
  have eq2356920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1312655 eq2356847
    | exact resolve eq2356847 eq1312655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2356847
  have eq2356977 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have r₁ := eq2356920
       have r₂ := eq28
       grind)
    | exact resolve eq2356920 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2356920
  have eq2357017 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2356977 eq52
    | exact resolve eq52 eq2356977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq2356977
  have eq2357064 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1312655 eq2357017
    | exact resolve eq2357017 eq1312655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312655 eq2357017
  have eq2357074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq2357064
    | exact resolve eq2357064 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2357064
  have eq2357078 : False := by grind
  exact eq2357078

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
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
  have eq99 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq100 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq141 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 (σ X0) X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq21
    | exact resolve eq21 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq100 (σ X1) (σ X0)
       grind)
    | exact superpose eq100 eq15
    | (have j1 := eq100 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq100 X1 (τ X0)
       grind)
    | exact superpose eq100 eq17
    | (have j1 := eq100 (τ X0) X1
       grind)
    | exact resolve eq17 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq100
  have eq215 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq42 (M.op X0 X0)
       grind)
    | exact superpose eq42 eq141
    | exact resolve eq141 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq988 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq205 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq205
    | exact resolve eq205 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq1029 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq988 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq988
    | (have j0 := eq988 X0 X1
       grind)
    | exact resolve eq988 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1503 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq203 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq203 X0 X1
       grind)
    | exact superpose eq203 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq203 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq203 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq203 X0 X0
       grind)
    | exact resolve eq12 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1505 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq203 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq203 X0 X1
       grind)
    | exact superpose eq203 eq13
    | (have j1 := eq203 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq203 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq203 X0 X1
       grind)
    | exact resolve eq13 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq1515 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1505 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505
  have eq1523 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1515 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1515
    | (have j0 := eq1515 X0 X1
       grind)
    | exact resolve eq1515 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515
  have eq1524 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1523 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1526 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1503 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq1503
    | (have j0 := eq1503 X0 X1
       grind)
    | exact resolve eq1503 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq1543 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1524 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq1524
    | (have j0 := eq1524 X0 X1
       grind)
    | exact resolve eq1524 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq1544 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1526 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1526
    | (have j0 := eq1526 X0 X1
       grind)
    | exact resolve eq1526 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1545 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1544 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1552 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1545 X0 X1
       have j1 := eq1543 X0 X1
       grind)
    | (have r₁ := eq1545 X0 X1
       have r₂ := eq1543 X0 X1
       grind)
    | exact resolve eq1545 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543 eq1545
  have eq1575 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1552 x y
       grind)
    | exact superpose eq1552 eq16
    | exact resolve eq16 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq1660 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1575
       have i₂ := eq1029 x y
       grind)
    | exact superpose eq1029 eq1575
    | (have j1 := eq1029 x y
       grind)
    | (have r₁ := eq1575
       have r₂ := eq1029 x y
       grind)
    | exact resolve eq1575 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029 eq1575
  have eq1661 : (M.op x y) = (M.op y x) := by grind
  clear eq1660
  have eq1725 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 x X0 y
       have i₂ := eq1661
       grind)
    | exact superpose eq1661 eq21
    | exact resolve eq21 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1732 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1725 X0 x
       have i₂ := eq21 x y X0 x
       grind)
    | exact superpose eq21 eq1725
    | exact resolve eq1725 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1725
  have eq1749 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op (M.op y x) (M.op y x)))) := by
    intro X0
    first
    | (have i₁ := eq215 y x
       have i₂ := eq1732 y
       grind)
    | exact superpose eq1732 eq215
    | exact resolve eq215 eq1732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1793 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq1749 X0
       have i₂ := eq1661
       grind)
    | exact superpose eq1661 eq1749
    | exact resolve eq1749 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661 eq1749
  have eq1810 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op (M.op x x) (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq1793 X0
       have i₂ := eq1732 x
       grind)
    | exact superpose eq1732 eq1793
    | exact resolve eq1793 eq1732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793
  have eq1826 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1810 X0
       have i₂ := eq215 x X0
       grind)
    | exact superpose eq215 eq1810
    | exact resolve eq1810 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq1810
  have eq2102 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1826 (σ x)
       grind)
    | exact superpose eq1826 eq16
    | exact resolve eq16 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826
  have eq2118 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2102
       have i₂ := eq42 x
       grind)
    | exact superpose eq42 eq2102
    | exact resolve eq2102 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2102
  have eq2148 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2118
       have i₂ := eq1732 x
       grind)
    | exact superpose eq1732 eq2118
    | exact resolve eq2118 eq1732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732 eq2118
  have eq2149 : False := by grind
  exact eq2149

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pxx_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq64 : (M.op x y) ≠ (M.op x x) ∨ (k y x) = (M.op y y) := by
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq43
    | exact resolve eq43 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq73 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq14 X0 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq14
    | (have j1 := eq11 X1 X0
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq95 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89 X0 X1 X2
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq89
    | (have j0 := eq89 X0 X1 X2
       grind)
    | exact resolve eq89 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq113 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq114 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq116 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq114
    | exact resolve eq114 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq118 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq116
    | exact resolve eq116 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq116
  have eq237 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq239 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq237 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq237
    | exact resolve eq237 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq248 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq251 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq248 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq248
    | exact resolve eq248 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq953 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq6173 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq953 X0 X1
       have j1 := eq95 X1 X0 x
       grind)
    | (have r₁ := eq953 X0 X1
       have r₂ := eq95 X0 X1 X0
       grind)
    | (have r₁ := eq953 X1 X0
       have r₂ := eq95 X0 X1 X1
       grind)
    | (have r₁ := eq953 X0 X0
       have r₂ := eq95 X0 X0 x
       grind)
    | exact resolve eq953 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq953
  have eq6326 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq6173 x y
       grind)
    | exact superpose eq6173 eq44
    | (have j1 := eq6173 x y
       grind)
    | exact resolve eq44 eq6173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6453 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq6326
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6326
    | exact resolve eq6326 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6326
  have eq6503 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq6453
    | exact resolve eq6453 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6453
  have eq6513 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq6503
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6503
    | exact resolve eq6503 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6503
  have eq6535 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq6513 eq6173
    | (have j0 := eq6173 (σ x) (σ y)
       grind)
    | exact resolve eq6173 eq6513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6539 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq6535
    | exact resolve eq6535 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6535
  have eq6551 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq6539
       have r₂ := eq27
       grind)
    | exact resolve eq6539 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6539
  have eq6558 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq6551
    | exact resolve eq6551 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6551
  have eq6574 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) X0) ∨ (M.op (σ x) (σ y)) = (k X0 (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq6558 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq6558
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq6558
       grind)
    | exact resolve eq12 eq6558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6575 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq6558 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq6558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6558
  have eq7631 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq6574
    | (have j0 := eq6574 (σ x)
       grind)
    | (have r₁ := eq6574 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq6574 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6574
  have eq7632 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq7631
  have eq7823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq7632 eq6513
    | exact resolve eq6513 eq7632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7632
  have eq7828 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq7823
  have eq7830 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq7828
       have r₂ := eq27
       grind)
    | exact resolve eq7828 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7828
  have eq7834 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq7830 eq6575
    | (have j0 := eq6575 (σ x)
       grind)
    | (have r₁ := eq6575 (σ x)
       have r₂ := eq7830
       grind)
    | exact resolve eq6575 eq7830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6575
  have eq7837 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) ∨ (M.op x y) = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq7830 eq54
    | exact resolve eq54 eq7830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7830
  have eq7849 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq7834
  have eq7850 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq7849
  have eq7852 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq251 eq7837
    | exact resolve eq7837 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq7837
  have eq8044 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq7850 eq6513
    | exact resolve eq6513 eq7850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6513 eq7850
  have eq8050 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq8044
  have eq8395 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq7852
    | (have j0 := eq7852 (σ x)
       grind)
    | exact resolve eq7852 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7852
  have eq8504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq8395 eq8050
    | exact resolve eq8050 eq8395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8050 eq8395
  have eq8526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq8504
  have eq8534 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq8526
       have r₂ := eq27
       grind)
    | exact resolve eq8526 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8526
  have eq8540 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq8534
       grind)
    | exact superpose eq8534 eq118
    | exact resolve eq118 eq8534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq8549 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (M.op y X0) ∨ (M.op x y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq8534
       grind)
    | exact superpose eq8534 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq8534
       grind)
    | exact resolve eq12 eq8534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8534
  have eq8579 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq8540
    | exact resolve eq8540 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8540
  have eq8607 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq8579 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq8579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9292 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq8549 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8549
    | (have j0 := eq8549 x
       grind)
    | (have r₁ := eq8549 x
       have r₂ := eq18
       grind)
    | exact resolve eq8549 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8549
  have eq9294 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq9292
  have eq9299 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq9294
       grind)
    | exact superpose eq9294 eq44
    | exact resolve eq44 eq9294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq9294
  have eq9316 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq9299
    | exact resolve eq9299 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9299
  have eq9335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq9316 eq6173
    | (have j0 := eq6173 (σ x) (σ y)
       grind)
    | exact resolve eq6173 eq9316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9316
  have eq9340 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq9335
    | exact resolve eq9335 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9335
  have eq9352 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq9340
       have r₂ := eq27
       grind)
    | exact resolve eq9340 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9340
  have eq9359 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq8579 eq9352
    | exact resolve eq9352 eq8579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9352
  have eq9363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq9359
    | exact resolve eq9359 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9359
  have eq9367 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq9363
       have r₂ := eq27
       grind)
    | exact resolve eq9363 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9363
  have eq9377 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 y
       have i₂ := eq9367
       grind)
    | exact superpose eq9367 eq54
    | exact resolve eq54 eq9367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq9391 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq239 eq9377
    | exact resolve eq9377 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq9377
  have eq9431 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9391 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9391
    | (have j0 := eq9391 x
       grind)
    | exact resolve eq9391 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9582 : (M.op x y) ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq9431
       grind)
    | exact superpose eq9431 eq64
    | (have r₁ := eq64
       have r₂ := eq9431
       grind)
    | exact resolve eq64 eq9431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq9583 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq9431
       grind)
    | exact superpose eq9431 eq73
    | exact resolve eq73 eq9431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq9431
  have eq9612 : (k y x) = (M.op y y) := by grind
  clear eq9582
  have eq9624 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq9583
    | exact resolve eq9583 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9583
  have eq9625 : (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq9612
       have i₂ := eq9391 y
       grind)
    | exact superpose eq9391 eq9612
    | exact resolve eq9612 eq9391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9391 eq9612
  have eq9629 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq9625
       have i₂ := eq9367
       grind)
    | exact superpose eq9367 eq9625
    | exact resolve eq9625 eq9367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9367 eq9625
  have eq10333 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq9629
       grind)
    | exact superpose eq9629 eq113
    | exact resolve eq113 eq9629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq9629
  have eq10350 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq10333
    | exact resolve eq10333 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10333
  have eq10367 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq10350 eq6173
    | (have j0 := eq6173 (σ y) (σ x)
       grind)
    | exact resolve eq6173 eq10350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10350
  have eq10370 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq9624 eq10367
    | exact resolve eq10367 eq9624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10367
  have eq10371 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq10370
  have eq10405 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10371 eq8607
    | (have j0 := eq8607 (σ x)
       grind)
    | (have r₁ := eq8607 (σ x)
       have r₂ := eq10371
       grind)
    | exact resolve eq8607 eq10371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8607 eq10371
  have eq10421 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq10405
  have eq10425 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq9624 eq10421
    | exact resolve eq10421 eq9624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9624 eq10421
  have eq10592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq10425 eq6173
    | (have j0 := eq6173 (σ x) (σ y)
       grind)
    | exact resolve eq6173 eq10425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6173 eq10425
  have eq10595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq10592
    | exact resolve eq10592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10592
  have eq10606 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq10595
       have r₂ := eq27
       grind)
    | exact resolve eq10595 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10595
  have eq10617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8579 eq10606
    | exact resolve eq10606 eq8579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8579 eq10606
  have eq10623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10617
    | exact resolve eq10617 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq10617
  have eq10629 : False := by grind
  exact eq10629

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pxy_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
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
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
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
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq49 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq221 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq228 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq221 X0 X1
       have j1 := eq49 X1 X0
       grind)
    | (have r₁ := eq221 X1 X0
       have r₂ := eq49 X0 X1
       grind)
    | (have r₁ := eq221 X1 X1
       have r₂ := eq49 X1 X1
       grind)
    | exact resolve eq221 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq221
  have eq426 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq228 (σ X0) (σ X1)
       grind)
    | exact superpose eq228 eq15
    | exact resolve eq15 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq426 X0 X1
       have i₂ := eq228 X0 X1
       grind)
    | exact superpose eq228 eq426
    | exact resolve eq426 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq426
  have eq436 : False := by grind
  exact eq436

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxx_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op (M.op X2 X1) X0) X0) = (M.op (M.op (M.op X2 X1) X0) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) X0) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 X1) X1) X1
       have r₂ := eq9 X1 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (τ X1) X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq22
    | exact resolve eq22 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq84 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81
    | exact resolve eq81 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq83
    | exact resolve eq83 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq84
    | exact resolve eq84 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq84
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq10
    | exact resolve eq10 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq118 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op (M.op X2 X1) X0) X0) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq25 X0 X1 (M.op (M.op X2 X1) X0) X2
       grind)
    | exact superpose eq25 eq34
    | (have j0 := eq34 X0 X1 X2
       grind)
    | (have r₁ := eq34 (M.op (M.op x X1) X0) X1 X2
       have r₂ := eq25 X0 X1 (M.op (M.op x X1) X0) x
       grind)
    | (have r₁ := eq34 X1 (M.op (M.op x X1) X0) X2
       have r₂ := eq25 X0 X1 X1 x
       grind)
    | exact resolve eq34 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq132 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) X1) = (M.op (M.op (M.op X0 X1) X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq118 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq165 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X2 (σ X0) X1 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq25
    | exact resolve eq25 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq102 X1
       grind)
    | exact superpose eq102 eq61
    | (have j0 := eq61 X0 X1
       grind)
    | exact resolve eq61 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq102
  have eq603 : ∀ X0 X1 : G, (k (σ (M.op (M.op X0 (τ X1)) (τ X1))) X1) = (σ (M.op (M.op (M.op X0 (τ X1)) (τ X1)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op (M.op X0 (τ X1)) (τ X1))
       have i₂ := eq132 X0 (τ X1)
       grind)
    | exact superpose eq132 eq18
    | exact resolve eq18 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq132
  have eq5380 : ∀ X0 X1 : G, (k (σ (M.op X0 (τ X1))) X1) = (σ (M.op (M.op X0 (τ X1)) (τ X1))) ∨ (k (σ (M.op X0 (τ X1))) X1) = (σ (M.op (M.op X0 (τ X1)) (τ X1))) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq603 X0 X1
       have i₂ := eq477 (M.op X0 (τ X1)) X1
       grind)
    | exact superpose eq477 eq603
    | (have j1 := eq477 (M.op X0 (τ X1)) X1
       grind)
    | exact resolve eq603 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq5426 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (M.op (τ X1) (M.op X0 (τ X1))) ∨ (k (σ (M.op X0 (τ X1))) X1) = (σ (M.op (M.op X0 (τ X1)) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5380 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5380
  have eq188777 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (τ (M.op X1 X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5426 X0 X1
       have i₂ := eq477 X0 X1
       grind)
    | exact superpose eq477 eq5426
    | (have j1 := eq477 X0 X1
       grind)
    | exact resolve eq5426 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq5426
  have eq188921 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq188777 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188777
  have eq189066 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq188921 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq188921
    | exact resolve eq188921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188921
  have eq189556 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq189066 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq189066
    | (have j0 := eq189066 X0 X1
       grind)
    | exact resolve eq189066 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189066
  have eq189602 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq189556 X0 X1
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq189556
    | (have j0 := eq189556 X0 X1
       grind)
    | exact resolve eq189556 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq189556
  have eq190492 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq189602 X1 X0
       grind)
    | exact superpose eq189602 eq10
    | (have j1 := eq189602 X1 X0
       grind)
    | exact resolve eq10 eq189602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190796 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq190492 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq190492
    | (have j0 := eq190492 X0 X1
       grind)
    | exact resolve eq190492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190492
  have eq191465 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq190796 (σ X0) (σ X1)
       grind)
    | exact superpose eq190796 eq15
    | (have j1 := eq190796 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq190796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191730 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq191465 X0 X1
       have i₂ := eq95 X1
       grind)
    | exact superpose eq95 eq191465
    | (have j0 := eq191465 X0 X1
       grind)
    | exact resolve eq191465 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191465
  have eq215565 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq191730 x y
       grind)
    | exact superpose eq191730 eq16
    | (have j1 := eq191730 x y
       grind)
    | exact resolve eq16 eq191730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191730
  have eq216587 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq215565
       have i₂ := eq189602 y x
       grind)
    | exact superpose eq189602 eq215565
    | (have j1 := eq189602 y x
       grind)
    | (have r₁ := eq215565
       have r₂ := eq189602 y x
       grind)
    | exact resolve eq215565 eq189602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189602
  have eq216594 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq216587
  have eq216951 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq169 y (σ x)
       have i₂ := eq216594
       grind)
    | exact superpose eq216594 eq169
    | (have j0 := eq169 y (σ x)
       grind)
    | (have r₁ := eq169 y (σ x)
       have r₂ := eq216594
       grind)
    | exact resolve eq169 eq216594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq216594
  have eq217036 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq216951
  have eq217072 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq217036
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq217036
    | exact resolve eq217036 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217036
  have eq217106 : (M.op y y) = (M.op y x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq217072
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq217072
    | exact resolve eq217072 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217072
  have eq219641 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 y X0 y
       have i₂ := eq217106
       grind)
    | exact superpose eq217106 eq25
    | exact resolve eq25 eq217106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217106
  have eq219676 : ∀ X0 : G, (σ (k x y)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq219641 X0 x
       have i₂ := eq25 x x X0 y
       grind)
    | exact superpose eq25 eq219641
    | exact resolve eq219641 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219641
  have eq221921 : ∀ X0 : G, (k x y) = (τ (σ (M.op x x))) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq219676 X0
       grind)
    | exact superpose eq219676 eq10
    | (have j1 := eq219676 X0
       grind)
    | exact resolve eq10 eq219676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219676
  have eq222246 : ∀ X0 : G, (k x y) = (M.op x x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq221921 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq221921
    | (have j0 := eq221921 X0
       grind)
    | exact resolve eq221921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221921
  have eq223804 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq222246 X0
       have i₂ := eq190796 x y
       grind)
    | exact superpose eq190796 eq222246
    | (have j0 := eq222246 x
       have j1 := eq190796 y x
       grind)
    | exact resolve eq222246 eq190796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190796 eq222246
  have eq306901 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have j0 := eq223804 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223804
  have eq306902 : (M.op x y) = (M.op x x) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq306901
  have eq306926 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (M.op y y) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 y X0 x
       have i₂ := eq306902
       grind)
    | exact superpose eq306902 eq25
    | exact resolve eq25 eq306902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306902
  have eq306983 : ∀ X0 : G, (M.op y y) = (M.op y x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq306926 X0 x
       have i₂ := eq25 x x X0 x
       grind)
    | exact superpose eq25 eq306926
    | exact resolve eq306926 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306926
  have eq307232 : (M.op y x) ≠ (M.op y x) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have j0 := eq306983 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306983
  have eq307233 : (M.op y y) = (M.op y x) := by grind
  clear eq307232
  have eq307243 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq307233
       grind)
    | exact superpose eq307233 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq307233
       grind)
    | exact resolve eq12 eq307233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307246 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq165 y X0 X1
       have i₂ := eq307233
       grind)
    | exact superpose eq307233 eq165
    | exact resolve eq165 eq307233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq307375 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 y X0 y
       have i₂ := eq307233
       grind)
    | exact superpose eq307233 eq25
    | exact resolve eq25 eq307233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307233
  have eq307411 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq307375 X0 x
       have i₂ := eq25 x x X0 y
       grind)
    | exact superpose eq25 eq307375
    | exact resolve eq307375 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq307375
  have eq321238 : (k x y) = (M.op x x) := by
    first
    | (have j0 := eq307243 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307243
  have eq321304 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq215565
       have i₂ := eq321238
       grind)
    | exact superpose eq321238 eq215565
    | exact resolve eq215565 eq321238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215565 eq321238
  have eq321390 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq321304
       have i₂ := eq307411 x
       grind)
    | exact superpose eq307411 eq321304
    | exact resolve eq321304 eq307411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321304
  have eq321391 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by grind
  clear eq321390
  have eq321401 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq321391
       have i₂ := eq307411 y
       grind)
    | exact superpose eq307411 eq321391
    | exact resolve eq321391 eq307411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321391
  have eq321469 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op y x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq321401
       grind)
    | exact superpose eq321401 eq9
    | exact resolve eq9 eq321401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321401
  have eq321525 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq321469 X0
       have i₂ := eq307246 X0 X0
       grind)
    | exact superpose eq307246 eq321469
    | exact resolve eq321469 eq307246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307246 eq321469
  have eq321990 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq321525 (σ x)
       grind)
    | exact superpose eq321525 eq16
    | exact resolve eq16 eq321525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321525
  have eq322158 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq321990
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq321990
    | exact resolve eq321990 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq321990
  have eq322515 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq322158
       have i₂ := eq307411 x
       grind)
    | exact superpose eq307411 eq322158
    | exact resolve eq322158 eq307411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307411 eq322158
  have eq322516 : False := by grind
  exact eq322516

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxx_y_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op (M.op X2 X1) X0) X0) = (M.op (M.op (M.op X2 X1) X0) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) X0) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 X1) X1) X1
       have r₂ := eq9 X1 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (τ X1) X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq22
    | exact resolve eq22 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq84 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81
    | exact resolve eq81 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq83
    | exact resolve eq83 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq84
    | exact resolve eq84 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq84
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq10
    | exact resolve eq10 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq117 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op (M.op X2 X1) X0) X0) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq25 X0 X1 (M.op (M.op X2 X1) X0) X2
       grind)
    | exact superpose eq25 eq34
    | (have j0 := eq34 X0 X1 X2
       grind)
    | (have r₁ := eq34 (M.op (M.op x X1) X0) X1 X2
       have r₂ := eq25 X0 X1 (M.op (M.op x X1) X0) x
       grind)
    | (have r₁ := eq34 X1 (M.op (M.op x X1) X0) X2
       have r₂ := eq25 X0 X1 X1 x
       grind)
    | exact resolve eq34 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq131 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) X1) = (M.op (M.op (M.op X0 X1) X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq117 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq164 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X2 (σ X0) X1 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq25
    | exact resolve eq25 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq102 X1
       grind)
    | exact superpose eq102 eq61
    | (have j0 := eq61 X0 X1
       grind)
    | exact resolve eq61 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq102
  have eq594 : ∀ X0 X1 : G, (k (σ (M.op (M.op X0 (τ X1)) (τ X1))) X1) = (σ (M.op (M.op (M.op X0 (τ X1)) (τ X1)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op (M.op X0 (τ X1)) (τ X1))
       have i₂ := eq131 X0 (τ X1)
       grind)
    | exact superpose eq131 eq18
    | exact resolve eq18 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq131
  have eq5392 : ∀ X0 X1 : G, (k (σ (M.op X0 (τ X1))) X1) = (σ (M.op (M.op X0 (τ X1)) (τ X1))) ∨ (k (σ (M.op X0 (τ X1))) X1) = (σ (M.op (M.op X0 (τ X1)) (τ X1))) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq594 X0 X1
       have i₂ := eq469 (M.op X0 (τ X1)) X1
       grind)
    | exact superpose eq469 eq594
    | (have j1 := eq469 (M.op X0 (τ X1)) X1
       grind)
    | exact resolve eq594 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq5440 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (M.op (τ X1) (M.op X0 (τ X1))) ∨ (k (σ (M.op X0 (τ X1))) X1) = (σ (M.op (M.op X0 (τ X1)) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5392 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5392
  have eq188531 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (τ (M.op X1 X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5440 X0 X1
       have i₂ := eq469 X0 X1
       grind)
    | exact superpose eq469 eq5440
    | (have j1 := eq469 X0 X1
       grind)
    | exact resolve eq5440 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq5440
  have eq188670 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq188531 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188531
  have eq188813 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq188670 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq188670
    | exact resolve eq188670 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188670
  have eq189312 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq188813 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq188813
    | (have j0 := eq188813 X0 X1
       grind)
    | exact resolve eq188813 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188813
  have eq189358 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq189312 X0 X1
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq189312
    | (have j0 := eq189312 X0 X1
       grind)
    | exact resolve eq189312 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq189312
  have eq190263 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq189358 X1 X0
       grind)
    | exact superpose eq189358 eq10
    | (have j1 := eq189358 X1 X0
       grind)
    | exact resolve eq10 eq189358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190581 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq190263 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq190263
    | (have j0 := eq190263 X0 X1
       grind)
    | exact resolve eq190263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190263
  have eq192290 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq190581 (σ X0) (σ X1)
       grind)
    | exact superpose eq190581 eq15
    | (have j1 := eq190581 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq190581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192564 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq192290 X0 X1
       have i₂ := eq95 X1
       grind)
    | exact superpose eq95 eq192290
    | (have j0 := eq192290 X0 X1
       grind)
    | exact resolve eq192290 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192290
  have eq216274 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq192564 x y
       grind)
    | exact superpose eq192564 eq16
    | (have j1 := eq192564 x y
       grind)
    | exact resolve eq16 eq192564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192564
  have eq217054 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq216274
       have i₂ := eq189358 y x
       grind)
    | exact superpose eq189358 eq216274
    | (have j1 := eq189358 y x
       grind)
    | (have r₁ := eq216274
       have r₂ := eq189358 y x
       grind)
    | exact resolve eq216274 eq189358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189358
  have eq217063 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq217054
  have eq217344 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq168 y (σ x)
       have i₂ := eq217063
       grind)
    | exact superpose eq217063 eq168
    | (have j0 := eq168 y (σ x)
       grind)
    | (have r₁ := eq168 y (σ x)
       have r₂ := eq217063
       grind)
    | exact resolve eq168 eq217063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq217063
  have eq217431 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq217344
  have eq217468 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq217431
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq217431
    | exact resolve eq217431 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217431
  have eq217501 : (M.op y y) = (M.op y x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq217468
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq217468
    | exact resolve eq217468 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217468
  have eq219153 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 y X0 y
       have i₂ := eq217501
       grind)
    | exact superpose eq217501 eq25
    | exact resolve eq25 eq217501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217501
  have eq219189 : ∀ X0 : G, (σ (k x y)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq219153 X0 x
       have i₂ := eq25 x x X0 y
       grind)
    | exact superpose eq25 eq219153
    | exact resolve eq219153 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219153
  have eq220702 : ∀ X0 : G, (k x y) = (τ (σ (M.op x x))) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq219189 X0
       grind)
    | exact superpose eq219189 eq10
    | (have j1 := eq219189 X0
       grind)
    | exact resolve eq10 eq219189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219189
  have eq221042 : ∀ X0 : G, (k x y) = (M.op x x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq220702 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq220702
    | (have j0 := eq220702 X0
       grind)
    | exact resolve eq220702 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220702
  have eq221050 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq221042 X0
       have i₂ := eq190581 x y
       grind)
    | exact superpose eq190581 eq221042
    | (have j0 := eq221042 x
       have j1 := eq190581 y x
       grind)
    | exact resolve eq221042 eq190581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190581 eq221042
  have eq300465 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have j0 := eq221050 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221050
  have eq300466 : (M.op x y) = (M.op x x) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq300465
  have eq300494 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (M.op y y) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 y X0 x
       have i₂ := eq300466
       grind)
    | exact superpose eq300466 eq25
    | exact resolve eq25 eq300466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300466
  have eq300556 : ∀ X0 : G, (M.op y y) = (M.op y x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq300494 X0 x
       have i₂ := eq25 x x X0 x
       grind)
    | exact superpose eq25 eq300494
    | exact resolve eq300494 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300494
  have eq302434 : (M.op y x) ≠ (M.op y x) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have j0 := eq300556 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300556
  have eq302435 : (M.op y y) = (M.op y x) := by grind
  clear eq302434
  have eq302442 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq302435
       grind)
    | exact superpose eq302435 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq302435
       grind)
    | exact resolve eq12 eq302435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302445 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq164 y X0 X1
       have i₂ := eq302435
       grind)
    | exact superpose eq302435 eq164
    | exact resolve eq164 eq302435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq302573 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 y X0 y
       have i₂ := eq302435
       grind)
    | exact superpose eq302435 eq25
    | exact resolve eq25 eq302435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302435
  have eq302609 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq302573 X0 x
       have i₂ := eq25 x x X0 y
       grind)
    | exact superpose eq25 eq302573
    | exact resolve eq302573 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq302573
  have eq306870 : (k x y) = (M.op x x) := by
    first
    | (have j0 := eq302442 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302442
  have eq306937 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq216274
       have i₂ := eq306870
       grind)
    | exact superpose eq306870 eq216274
    | exact resolve eq216274 eq306870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216274 eq306870
  have eq307026 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq306937
       have i₂ := eq302609 x
       grind)
    | exact superpose eq302609 eq306937
    | exact resolve eq306937 eq302609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306937
  have eq307027 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by grind
  clear eq307026
  have eq307036 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq307027
       have i₂ := eq302609 y
       grind)
    | exact superpose eq302609 eq307027
    | exact resolve eq307027 eq302609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307027
  have eq307104 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op y x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq307036
       grind)
    | exact superpose eq307036 eq9
    | exact resolve eq9 eq307036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307036
  have eq307163 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq307104 X0
       have i₂ := eq302445 X0 X0
       grind)
    | exact superpose eq302445 eq307104
    | exact resolve eq307104 eq302445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302445 eq307104
  have eq307624 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq307163 (σ x)
       grind)
    | exact superpose eq307163 eq16
    | exact resolve eq16 eq307163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307163
  have eq307785 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq307624
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq307624
    | exact resolve eq307624 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq307624
  have eq308129 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq307785
       have i₂ := eq302609 x
       grind)
    | exact superpose eq302609 eq307785
    | exact resolve eq307785 eq302609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302609 eq307785
  have eq308130 : False := by grind
  exact eq308130

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
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
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq64 : (M.op x y) ≠ (M.op x x) ∨ (M.op y x) = (k y x) := by
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
  have eq65 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op (M.op X2 X1) X0) X0) = (k (M.op (M.op X2 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) X0) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X1) X1) X1
       have r₂ := eq14 X1 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq43
    | exact resolve eq43 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq49
    | exact resolve eq49 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq78 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq78
    | (have j0 := eq78 (σ X0) (σ X1)
       grind)
    | exact resolve eq78 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq78 x y
       grind)
    | exact superpose eq78 eq44
    | (have j1 := eq78 x y
       grind)
    | exact resolve eq44 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq102 : (τ (σ (M.op x y))) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq100 eq58
    | exact resolve eq58 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq100 eq78
    | (have j0 := eq78 (σ x) (σ y)
       grind)
    | exact resolve eq78 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq103
    | exact resolve eq103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq102
    | exact resolve eq102 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq107 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq104
       have r₂ := eq27
       grind)
    | exact resolve eq104 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq109 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq107
    | exact resolve eq107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq112 : y ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq113 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq125 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq129 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq125
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq125
    | exact resolve eq125 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq131 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq129
    | exact resolve eq129 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq138 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq143 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq67 sF1
       grind)
    | exact superpose eq67 eq140
    | exact resolve eq140 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq145 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq143
       have i₂ := eq67 sF0
       grind)
    | exact superpose eq67 eq143
    | exact resolve eq143 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq143
  have eq153 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq124
       grind)
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq131
       grind)
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq138 eq16
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq200 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq145 eq16
    | exact resolve eq16 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq78 (σ X0) sF3
       grind)
    | exact superpose eq78 eq40
    | (have j1 := eq78 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq258 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq260 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq258 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq258
    | exact resolve eq258 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq262 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq109 eq51
    | exact resolve eq51 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq271 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq268 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq268
    | exact resolve eq268 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq278 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (σ y)) X1)) = (M.op X1 (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq262 eq14
    | exact resolve eq14 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq283 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq278 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq278
    | exact resolve eq278 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq302 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq319 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (σ y)) ∨ (M.op (M.op (σ y) X1) X0) = (k (M.op (σ y) X1) X0) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq283 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ y) X0)
       have r₂ := eq283 X0 (M.op (σ y) X0)
       grind)
    | (have r₁ := eq13 (M.op (σ y) X0) (σ y)
       have r₂ := eq283 X0 (σ y)
       grind)
    | exact resolve eq13 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq350 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq408 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op (M.op X2 X1) X3) X0) = (k (M.op (M.op X2 X1) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) X3) X0
       have i₂ := eq54 X3 X1 X0 X2
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | (have r₁ := eq13 X1 (M.op (M.op X3 X1) X0)
       have r₂ := eq54 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | (have r₁ := eq13 (M.op (M.op X3 X1) X0) X1
       have r₂ := eq54 X0 X1 X1 X3
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X1) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (M.op X3 (M.op (M.op X0 X1) X2)) = (k X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op (M.op X0 X1) X2)
       have i₂ := eq54 X2 X1 (M.op (M.op X0 X1) X2) X0
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X3 (M.op (M.op X0 X1) X2)
       grind)
    | (have r₁ := eq13 X1 (M.op (M.op X3 X1) X0)
       have r₂ := eq54 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | (have r₁ := eq13 (M.op (M.op X3 X1) X0) X1
       have r₂ := eq54 X0 X1 X1 X3
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X1) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (M.op X3 X1) = (k X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq410 X0 X1 X2 X3
       have i₂ := eq54 X2 X1 X3 X0
       grind)
    | exact superpose eq54 eq410
    | (have j0 := eq410 X0 X1 X2 X3
       grind)
    | (have r₁ := eq410 X0 X1 X2 (M.op (M.op X3 X1) X0)
       have r₂ := eq54 X0 X1 (M.op (M.op X0 X1) X2) X3
       grind)
    | (have r₁ := eq410 X0 (M.op (M.op X3 X1) X0) X2 X1
       have r₂ := eq54 X0 X1 (M.op (M.op X0 (M.op (M.op X3 X1) X0)) X2) X3
       grind)
    | exact resolve eq410 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq494 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq109 eq113
    | (have r₁ := eq113
       have r₂ := eq109
       grind)
    | exact resolve eq113 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq113
  have eq495 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq494
  have eq498 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq495 eq100
    | exact resolve eq100 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq495 eq58
    | exact resolve eq58 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq495
  have eq501 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq498
  have eq504 : (k x y) = (M.op x x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq72 eq499
    | exact resolve eq499 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq508 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq501 eq166
    | exact resolve eq166 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ x)) X0)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq501 eq14
    | exact resolve eq14 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq518 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq513 X0
       have i₂ := eq14 X0 sF2 sF3
       grind)
    | exact superpose eq14 eq513
    | exact resolve eq513 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq555 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq560 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq555 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq555
    | (have j0 := eq555 X0 X1
       grind)
    | exact resolve eq555 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq571 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq518
    | (have j0 := eq518 (σ x)
       grind)
    | exact resolve eq518 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq601 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq571 eq65
    | (have r₁ := eq65
       have r₂ := eq571
       grind)
    | exact resolve eq65 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq571
  have eq609 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq601
  have eq621 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq609 eq153
    | exact resolve eq153 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq652 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X1) = (k (M.op (M.op X0 X1) X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq667 : (k y x) = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq621 eq508
    | exact resolve eq508 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq621
  have eq671 : (k y x) = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq667
  have eq689 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq504
       grind)
    | exact superpose eq504 eq105
    | exact resolve eq105 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq504
  have eq692 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq689
  have eq709 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ x)) X0)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq692 eq14
    | exact resolve eq14 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq714 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq709 X0
       have i₂ := eq14 X0 sF2 sF3
       grind)
    | exact superpose eq14 eq709
    | exact resolve eq709 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq762 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq714
    | (have j0 := eq714 (σ x)
       grind)
    | exact resolve eq714 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq1268 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq302 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq302
    | (have j0 := eq302 X0 y
       grind)
    | exact resolve eq302 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq1464 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq350 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq350
    | (have j0 := eq350 x X0
       grind)
    | exact resolve eq350 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1465 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq350 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq350
    | (have j0 := eq350 y X0
       grind)
    | exact resolve eq350 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq3892 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (k (M.op (σ y) X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq319 (σ y) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq4629 : ∀ X0 X1 : G, (σ X1) ≠ (k X0 (σ X1)) ∨ (σ X1) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq558 (τ X0) X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq558
    | (have j0 := eq558 (τ X0) X1
       grind)
    | exact resolve eq558 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq4674 : ∀ X0 X1 : G, (σ X1) ≠ (k X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4629 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4629
    | (have j0 := eq4629 X0 X1
       grind)
    | exact resolve eq4629 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4629
  have eq4797 : (M.op (M.op (M.op x y) y) y) = (k (M.op (M.op x y) y) y) := by
    first
    | (have i₁ := eq652 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq652
    | (have j0 := eq652 x y
       grind)
    | exact resolve eq652 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq7575 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X1) = (k (M.op (M.op X0 X1) X2) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq408 X1 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq8418 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq416 X1 X0 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq9825 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq560
    | (have j0 := eq560 X0 X1
       grind)
    | exact resolve eq560 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq560
  have eq9962 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9825 y x
       have i₂ := eq671
       grind)
    | exact superpose eq671 eq9825
    | (have j0 := eq9825 y x
       grind)
    | exact resolve eq9825 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq9978 : (k (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9825 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq9825
    | (have j0 := eq9825 x y
       grind)
    | exact resolve eq9825 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10022 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq9962
  have eq10042 : (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9978
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq9978
    | exact resolve eq9978 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9978
  have eq10052 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10022
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10022
    | exact resolve eq10022 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10022
  have eq10098 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10042
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10042
    | exact resolve eq10042 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10042
  have eq10108 : (k (σ x) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10052
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10052
    | exact resolve eq10052 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10052
  have eq10133 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10098
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10098
    | exact resolve eq10098 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10098
  have eq10143 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10108
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10108
    | exact resolve eq10108 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10108
  have eq10160 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10133
       have i₂ := eq124
       grind)
    | exact superpose eq124 eq10133
    | exact resolve eq10133 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10133
  have eq10167 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq10143
    | exact resolve eq10143 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10143
  have eq10182 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10160
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10160
    | exact resolve eq10160 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10160
  have eq10187 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10167
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10167
    | exact resolve eq10167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10167
  have eq10200 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10182
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10182
    | exact resolve eq10182 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10182
  have eq10205 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10187
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10187
    | exact resolve eq10187 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10187
  have eq10208 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq10200
    | exact resolve eq10200 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10200
  have eq10216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10205 eq100
    | exact resolve eq100 eq10205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10205
  have eq10222 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq10216
  have eq10226 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq10222
       have r₂ := eq27
       grind)
    | exact resolve eq10222 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10222
  have eq10262 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10226 eq3892
    | exact resolve eq3892 eq10226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10226
  have eq10286 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq10262
  have eq10325 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq10286
    | exact resolve eq10286 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10286
  have eq10356 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10325 eq100
    | exact resolve eq100 eq10325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10325
  have eq10362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq10356
  have eq10366 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10362
       have r₂ := eq27
       grind)
    | exact resolve eq10362 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10362
  have eq10373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10366 eq762
    | exact resolve eq762 eq10366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq10366
  have eq10402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq10373
  have eq10407 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10402
       have r₂ := eq27
       grind)
    | exact resolve eq10402 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10402
  have eq10676 : (M.op x y) ≠ (M.op x y) ∨ (M.op y x) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq10407
       grind)
    | exact superpose eq10407 eq64
    | (have r₁ := eq64
       have r₂ := eq10407
       grind)
    | exact resolve eq64 eq10407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq10687 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 x
       have i₂ := eq10407
       grind)
    | exact superpose eq10407 eq54
    | exact resolve eq54 eq10407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10407
  have eq10702 : (M.op y x) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq10676
  have eq10705 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq260 eq10687
    | exact resolve eq10687 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10687
  have eq10717 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq10702
       grind)
    | exact superpose eq10702 eq124
    | exact resolve eq124 eq10702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq10702
  have eq10787 : (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq131
       have i₂ := eq10705 y
       grind)
    | exact superpose eq10705 eq131
    | exact resolve eq131 eq10705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10705
  have eq10968 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10717
       have i₂ := eq10787
       grind)
    | exact superpose eq10787 eq10717
    | exact resolve eq10717 eq10787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10717 eq10787
  have eq11010 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10968
  have eq11016 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11010 eq153
    | exact resolve eq153 eq11010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq11010
  have eq11032 : (k y x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq166 eq11016
    | exact resolve eq11016 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11016
  have eq11284 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9825 y x
       have i₂ := eq11032
       grind)
    | exact superpose eq11032 eq9825
    | (have j0 := eq9825 y x
       grind)
    | exact resolve eq9825 eq11032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9825 eq11032
  have eq11288 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq11284
  have eq11294 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11288
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq11288
    | exact resolve eq11288 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11288
  have eq11299 : (k (σ x) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11294
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11294
    | exact resolve eq11294 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11294
  have eq11302 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11299
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11299
    | exact resolve eq11299 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11299
  have eq11305 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11302
    | exact resolve eq11302 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11302
  have eq11307 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11305
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11305
    | exact resolve eq11305 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11305
  have eq11308 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11307
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11307
    | exact resolve eq11307 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11307
  have eq12025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11308 eq100
    | exact resolve eq100 eq11308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11308
  have eq12032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq12025
  have eq12036 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12032
       have r₂ := eq27
       grind)
    | exact resolve eq12032 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12032
  have eq12073 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12036 eq3892
    | exact resolve eq3892 eq12036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3892 eq12036
  have eq12099 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12073
  have eq12138 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq12099
    | exact resolve eq12099 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12099
  have eq12144 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12138 eq100
    | exact resolve eq100 eq12138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq12138
  have eq12152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12144
  have eq12155 : y = (M.op x y) := by
    first
    | (have r₁ := eq12152
       have r₂ := eq27
       grind)
    | exact resolve eq12152 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12152
  have eq12396 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq12155 eq20
    | exact resolve eq20 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12399 : y ≠ y ∨ (M.op y x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | exact superpose eq12155 eq112
    | (have r₁ := eq112
       have r₂ := eq12155
       grind)
    | exact resolve eq112 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq12404 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq12155 eq260
    | exact resolve eq260 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq12410 : (k x y) = (M.op x x) ∨ (M.op y x) = (M.op y y) := by grind
  clear eq12399
  have eq12420 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12396
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12396
    | exact resolve eq12396 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12396
  have eq12423 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq12420 eq26
    | exact resolve eq26 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq12435 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq12420 eq219
    | exact resolve eq219 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq14719 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq12410
       grind)
    | exact superpose eq12410 eq44
    | exact resolve eq44 eq12410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12410
  have eq14738 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq14719
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq14719
    | exact resolve eq14719 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14719
  have eq14748 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ (M.op y x) = (M.op y y) := by
    first
    | exact superpose eq12420 eq14738
    | exact resolve eq14738 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14738
  have eq15031 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op y x) = (M.op y y) := by
    first
    | exact superpose eq14748 eq78
    | (have j0 := eq78 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq78 eq14748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14748
  have eq15040 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op y x) = (M.op y y) := by
    first
    | exact superpose eq12423 eq15031
    | exact resolve eq15031 eq12423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15031
  have eq15043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y x) = (M.op y y) := by
    first
    | exact superpose eq12423 eq15040
    | exact resolve eq15040 eq12423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15040
  have eq15046 : (M.op y x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq15043
       have r₂ := eq27
       grind)
    | exact resolve eq15043 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15043
  have eq18691 : (σ (k x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq12435 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12435
    | (have j0 := eq12435 x
       grind)
    | exact resolve eq12435 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12435
  have eq18727 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq12423 eq18691
    | exact resolve eq18691 eq12423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18691
  have eq18755 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq18727
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq18727
    | exact resolve eq18727 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18727
  have eq18771 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq12420 eq18755
    | exact resolve eq18755 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18755
  have eq18777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq12423 eq18771
    | exact resolve eq18771 eq12423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18771
  have eq18780 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq18777
       have r₂ := eq27
       grind)
    | exact resolve eq18777 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18777
  have eq18789 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq18780 eq62
    | exact resolve eq62 eq18780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq18800 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12155 eq18789
    | exact resolve eq18789 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18789
  have eq19155 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq12420 eq1268
    | exact resolve eq1268 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq19167 : (k (M.op y y) y) = (τ (k (M.op (σ y) (σ y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq166 eq19155
    | exact resolve eq19155 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19155
  have eq19250 : (k (M.op y y) y) = (τ (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | exact superpose eq12420 eq19167
    | exact resolve eq19167 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19167
  have eq19376 : (k x (M.op y y)) = (τ (k (σ x) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq166 eq1464
    | exact resolve eq1464 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19453 : (k x (M.op y y)) = (τ (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq12420 eq19376
    | exact resolve eq19376 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19376
  have eq19528 : (σ (k (M.op y y) y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq19250 eq15
    | exact resolve eq15 eq19250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19547 : (k x (k (M.op y y) y)) = (τ (k (σ x) (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))))) := by
    first
    | exact superpose eq19250 eq1464
    | exact resolve eq1464 eq19250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19597 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq12420 eq1465
    | exact resolve eq1465 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq19609 : (k y (M.op y y)) = (τ (k (σ (M.op x y)) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq166 eq19597
    | exact resolve eq19597 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq19597
  have eq19696 : (k y (M.op y y)) = (τ (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq12420 eq19609
    | exact resolve eq19609 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19609
  have eq19854 : (σ (k x (M.op y y))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq19453 eq15
    | exact resolve eq15 eq19453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19453
  have eq20328 : (σ (k y (M.op y y))) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq19696 eq15
    | exact resolve eq15 eq19696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19696
  have eq21132 : (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op x (M.op y y))) ∨ (M.op y y) = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq19854
       have i₂ := eq78 x (M.op y y)
       grind)
    | exact superpose eq78 eq19854
    | (have j1 := eq78 x (M.op y y)
       grind)
    | exact resolve eq19854 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19854
  have eq21207 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op y y) = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq21132
       have i₂ := eq12404 x y
       grind)
    | exact superpose eq12404 eq21132
    | exact resolve eq21132 eq12404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21132
  have eq21218 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op y y) = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq21207
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21207
    | exact resolve eq21207 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21207
  have eq21227 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op y y) = (M.op x (M.op y y)) := by
    first
    | exact superpose eq20 eq21218
    | exact resolve eq21218 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21218
  have eq21236 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq21227
       have i₂ := eq12404 x y
       grind)
    | exact superpose eq12404 eq21227
    | exact resolve eq21227 eq12404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21227
  have eq21245 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq21236
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21236
    | exact resolve eq21236 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21236
  have eq21252 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq12155 eq21245
    | exact resolve eq21245 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21245
  have eq22047 : (k (M.op y y) y) = (M.op (M.op y y) y) := by
    first
    | exact superpose eq12155 eq4797
    | exact resolve eq4797 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4797
  have eq22064 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (σ (M.op (M.op y y) y)) := by
    first
    | (have i₁ := eq19528
       have i₂ := eq22047
       grind)
    | exact superpose eq22047 eq19528
    | exact resolve eq19528 eq22047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19528
  have eq22908 : ∀ X0 : G, (M.op y y) = (k y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq8418 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8418
    | (have j0 := eq8418 y x X0
       grind)
    | exact resolve eq8418 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23043 : ∀ X0 : G, (M.op y y) = (k y (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq12155 eq22908
    | exact resolve eq22908 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22908
  have eq23215 : (σ (M.op y y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq20328
       have i₂ := eq23043 y
       grind)
    | exact superpose eq23043 eq20328
    | exact resolve eq20328 eq23043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20328 eq23043
  have eq23241 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq23215
       have i₂ := eq131
       grind)
    | exact superpose eq131 eq23215
    | exact resolve eq23215 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq23215
  have eq23256 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq12420 eq23241
    | exact resolve eq23241 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23241
  have eq23296 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq23256 eq78
    | (have j0 := eq78 (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq78 eq23256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23308 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by grind
  clear eq23296
  have eq23326 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq23308 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))
       have r₂ := eq23308
       grind)
    | exact resolve eq13 eq23308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23328 : ∀ X0 X1 : G, (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op X0 (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq23308 eq54
    | exact resolve eq54 eq23308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23308
  have eq23343 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by grind
  clear eq23326
  have eq23345 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq23328 x X0
       have i₂ := eq54 X0 sF1 x sF1
       grind)
    | exact superpose eq54 eq23328
    | exact resolve eq23328 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23328
  have eq23558 : (k (M.op y y) y) = (τ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | exact superpose eq23343 eq19250
    | exact resolve eq19250 eq23343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19250
  have eq23567 : (M.op (M.op y y) y) = (τ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq23558
       have i₂ := eq22047
       grind)
    | exact superpose eq22047 eq23558
    | exact resolve eq23558 eq22047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23558
  have eq29844 : (k x (k (M.op y y) y)) = (τ (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))))) := by
    first
    | exact superpose eq23343 eq19547
    | exact resolve eq19547 eq23343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19547
  have eq29845 : (k x (M.op (M.op y y) y)) = (τ (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq29844
       have i₂ := eq22047
       grind)
    | exact superpose eq22047 eq29844
    | exact resolve eq29844 eq22047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22047 eq29844
  have eq32316 : (σ (k x (M.op (M.op y y) y))) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | exact superpose eq29845 eq15
    | exact resolve eq15 eq29845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40575 : (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) = (σ (k x (M.op (M.op y x) y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq32316
       have i₂ := eq15046
       grind)
    | exact superpose eq15046 eq32316
    | exact resolve eq32316 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15046
  have eq40588 : (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) = (σ (M.op x (M.op (M.op y y) y))) ∨ (M.op (M.op y y) y) = (M.op x (M.op (M.op y y) y)) := by
    first
    | (have i₁ := eq32316
       have i₂ := eq78 x (M.op (M.op y y) y)
       grind)
    | exact superpose eq78 eq32316
    | (have j1 := eq78 x (M.op (M.op y y) y)
       grind)
    | exact resolve eq32316 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40672 : (σ (M.op x y)) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ (M.op (M.op y y) y) = (M.op x (M.op (M.op y y) y)) := by
    first
    | (have i₁ := eq40588
       have i₂ := eq54 y y x y
       grind)
    | exact superpose eq54 eq40588
    | exact resolve eq40588 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40588
  have eq40675 : (σ (M.op x x)) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq40575
       have i₂ := eq8418 x y y
       grind)
    | exact superpose eq8418 eq40575
    | exact resolve eq40575 eq8418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40575
  have eq40687 : (σ (M.op x y)) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ (M.op (M.op y y) y) = (M.op x (M.op (M.op y y) y)) := by
    first
    | (have i₁ := eq40672
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq40672
    | exact resolve eq40672 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40672
  have eq40690 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq40675
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq40675
    | exact resolve eq40675 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq40675
  have eq40700 : (σ (M.op x y)) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ (M.op (M.op y y) y) = (M.op x (M.op (M.op y y) y)) := by
    first
    | exact superpose eq20 eq40687
    | exact resolve eq40687 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq40687
  have eq40709 : (M.op x y) = (M.op (M.op y y) y) ∨ (σ (M.op x y)) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq40700
       have i₂ := eq54 y y x y
       grind)
    | exact superpose eq54 eq40700
    | exact resolve eq40700 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40700
  have eq40718 : (M.op x y) = (M.op (M.op y y) y) ∨ (σ (M.op x y)) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq40709
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq40709
    | exact resolve eq40709 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40709
  have eq40726 : (σ (M.op x y)) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq12155 eq40718
    | exact resolve eq40718 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40718
  have eq41721 : (τ (σ (M.op x y))) = (k x (M.op (M.op y y) y)) ∨ y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq40726 eq29845
    | exact resolve eq29845 eq40726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29845
  have eq41722 : (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq40726 eq78
    | (have j0 := eq78 (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))
       grind)
    | exact resolve eq78 eq40726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41741 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ y = (M.op (M.op y y) y) := by
    first
    | (have i₁ := eq41722
       have i₂ := eq54 sF1 sF1 sF2 sF1
       grind)
    | exact superpose eq54 eq41722
    | exact resolve eq41722 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41722
  have eq41742 : (M.op x y) = (k x (M.op (M.op y y) y)) ∨ y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq30 eq41721
    | exact resolve eq41721 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq41721
  have eq41752 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq12423 eq41741
    | exact resolve eq41741 eq12423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41741
  have eq41753 : y = (k x (M.op (M.op y y) y)) ∨ y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq12155 eq41742
    | exact resolve eq41742 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41742
  have eq41761 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ y = (M.op (M.op y y) y) := by
    first
    | (have r₁ := eq41752
       have r₂ := eq27
       grind)
    | exact resolve eq41752 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41752
  have eq41769 : (M.op (σ x) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ y = (M.op (M.op y y) y) := by
    first
    | (have i₁ := eq41761
       have i₂ := eq54 sF1 sF1 sF2 sF1
       grind)
    | exact superpose eq54 eq41761
    | exact resolve eq41761 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41761
  have eq41775 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq12423 eq41769
    | exact resolve eq41769 eq12423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41769
  have eq41781 : (τ (M.op (σ x) (σ y))) = (M.op (M.op y y) y) ∨ y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq41775 eq23567
    | exact resolve eq23567 eq41775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23567 eq41775
  have eq43381 : y ≠ (τ (M.op (σ x) (σ y))) ∨ y = (M.op (M.op y y) y) := by grind
  have eq47581 : y = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op (M.op y y) y) := by
    first
    | (have i₁ := eq41753
       have i₂ := eq41781
       grind)
    | exact superpose eq41781 eq41753
    | exact resolve eq41753 eq41781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41753 eq41781
  have eq47613 : y = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (M.op (M.op y y) y) := by
    first
    | (have r₁ := eq47581
       have r₂ := eq43381
       grind)
    | exact resolve eq47581 eq43381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43381 eq47581
  have eq47630 : y = (M.op (M.op y y) y) ∨ y = (τ (k (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq47613
       have i₂ := eq1464 sF4
       grind)
    | exact superpose eq1464 eq47613
    | exact resolve eq47613 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464 eq47613
  have eq47735 : (σ (k x y)) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ y = (τ (k (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq32316
       have i₂ := eq47630
       grind)
    | exact superpose eq47630 eq32316
    | exact resolve eq32316 eq47630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32316 eq47630
  have eq47773 : (k (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ y = (τ (k (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq47735
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq47735
    | exact resolve eq47735 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq47735
  have eq47777 : (k (σ x) (σ (M.op x y))) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ y = (τ (k (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq12420 eq47773
    | exact resolve eq47773 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47773
  have eq47780 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ y = (τ (k (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq18780 eq47777
    | exact resolve eq47777 eq18780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47777
  have eq48713 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (k X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq145 eq4674
    | exact resolve eq4674 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq4674
  have eq48848 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (k X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq23345 eq48713
    | (have j0 := eq48713 X0
       grind)
    | exact resolve eq48713 eq23345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48713
  have eq58710 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) y) = (k (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq7575 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7575
    | (have j0 := eq7575 x y X0
       grind)
    | exact resolve eq7575 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7575
  have eq58912 : ∀ X0 : G, (M.op (M.op y X0) y) = (k (M.op y X0) y) := by
    intro X0
    first
    | exact superpose eq12155 eq58710
    | exact resolve eq58710 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58710
  have eq64178 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (τ (k (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40690 eq47780
    | exact resolve eq47780 eq40690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47780
  have eq64180 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40690 eq78
    | (have j0 := eq78 (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))
       grind)
    | exact resolve eq78 eq40690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64193 : y = (τ (k (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq64178
  have eq64215 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq64180
       have i₂ := eq54 sF1 sF1 sF2 sF1
       grind)
    | exact superpose eq54 eq64180
    | exact resolve eq64180 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64180
  have eq64239 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12423 eq64215
    | exact resolve eq64215 eq12423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64215
  have eq64240 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by grind
  clear eq64239
  have eq64250 : (M.op (σ x) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq64240
       have i₂ := eq54 sF1 sF1 sF2 sF1
       grind)
    | exact superpose eq54 eq64240
    | exact resolve eq64240 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64240
  have eq64259 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12423 eq64250
    | exact resolve eq64250 eq12423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64250
  have eq64277 : ∀ X0 : G, (σ (k y X0)) = (k (k (σ x) (M.op (σ x) (σ y))) (σ X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq64193 eq34
    | exact resolve eq34 eq64193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq64193
  have eq64922 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq64259 eq40690
    | exact resolve eq40690 eq64259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40690 eq64259
  have eq64970 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq64922
  have eq65455 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12420 eq10208
    | exact resolve eq10208 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10208
  have eq65456 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq65455
       have r₂ := eq27
       grind)
    | exact resolve eq65455 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65455
  have eq65457 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12420 eq65456
    | exact resolve eq65456 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65456
  have eq65458 : (k (σ x) (σ (M.op x y))) ≠ (M.op (σ x) (σ x)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq12420 eq65457
    | exact resolve eq65457 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65457
  have eq65459 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq18780 eq65458
    | exact resolve eq65458 eq18780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18780 eq65458
  have eq95067 : ∀ X0 : G, (σ (k y (τ X0))) = (k (k (σ x) (M.op (σ x) (σ y))) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq64277 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq64277
    | exact resolve eq64277 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64277
  have eq95289 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ x) (M.op (σ x) (σ y))) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq95067 X0
       have i₂ := eq38 X0 y
       grind)
    | exact superpose eq38 eq95067
    | exact resolve eq95067 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq95067
  have eq95332 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ x) (M.op (σ x) (σ y))) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq95289 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95289
    | (have j0 := eq95289 X0
       grind)
    | exact resolve eq95289 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95289
  have eq95357 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (k (σ x) (M.op (σ x) (σ y))) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq12420 eq95332
    | exact resolve eq95332 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95332
  have eq95394 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (M.op (σ x) (σ x)) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq64970 eq95357
    | exact resolve eq95357 eq64970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64970 eq95357
  have eq95504 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (M.op (σ x) (σ x)) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq95394 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95394
  have eq95624 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq95504 eq48848
    | (have j0 := eq48848 (σ (M.op x y))
       grind)
    | exact resolve eq48848 eq95504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48848 eq95504
  have eq95753 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq95624
       have r₂ := eq23256
       grind)
    | exact resolve eq95624 eq23256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23256 eq95624
  have eq95831 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq95753 eq54
    | exact resolve eq54 eq95753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95753
  have eq95857 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq23345 eq95831
    | exact resolve eq95831 eq23345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23345 eq95831
  have eq96083 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq95857 eq65459
    | (have r₁ := eq65459
       have r₂ := eq95857 x
       grind)
    | exact resolve eq65459 eq95857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96181 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq95857
  have eq96194 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq96181
       have r₂ := eq12423
       grind)
    | exact resolve eq96181 eq12423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96181
  have eq96195 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq96083
       have r₂ := eq65459
       grind)
    | exact resolve eq96083 eq65459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65459 eq96083
  have eq96232 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq96195
       have r₂ := eq12423
       grind)
    | exact resolve eq96195 eq12423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12423 eq96195
  have eq96249 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq96194 eq72
    | exact resolve eq72 eq96194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq96296 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq96194 eq54
    | exact resolve eq54 eq96194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96321 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq271 eq96296
    | exact resolve eq96296 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq96296
  have eq96328 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq12420 eq96321
    | exact resolve eq96321 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96321
  have eq96467 : (k (M.op x y) x) = (τ (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq96232 eq185
    | exact resolve eq185 eq96232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq96232
  have eq96526 : (k y x) = (τ (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq12155 eq96467
    | exact resolve eq96467 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96467
  have eq96702 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (k (σ x) (M.op (M.op X0 (σ (M.op x y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq96328 eq8418
    | exact resolve eq8418 eq96328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8418
  have eq97046 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op X0 (σ (M.op x y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq96194 eq96702
    | exact resolve eq96702 eq96194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96194 eq96702
  have eq97169 : (k y x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq96328 eq96526
    | exact resolve eq96526 eq96328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96328 eq96526
  have eq97170 : (k y x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq200 eq97169
    | exact resolve eq97169 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq97169
  have eq97171 : (k y x) = (M.op y y) := by
    first
    | exact superpose eq12155 eq97170
    | exact resolve eq97170 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97170
  have eq97173 : (M.op y x) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq97171
       have i₂ := eq78 y x
       grind)
    | exact superpose eq78 eq97171
    | (have j1 := eq78 y x
       grind)
    | exact resolve eq97171 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq97171
  have eq98228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq97046 eq40726
    | exact resolve eq40726 eq97046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40726
  have eq98248 : y = (M.op (M.op y y) y) := by
    first
    | (have r₁ := eq98228
       have r₂ := eq27
       grind)
    | exact resolve eq98228 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98228
  have eq98269 : (σ y) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq22064
       have i₂ := eq98248
       grind)
    | exact superpose eq98248 eq22064
    | exact resolve eq22064 eq98248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22064 eq98248
  have eq98320 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq23343 eq98269
    | exact resolve eq98269 eq23343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23343 eq98269
  have eq98325 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq98320
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq98320
    | exact resolve eq98320 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98320
  have eq98329 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq12420 eq98325
    | exact resolve eq98325 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98325
  have eq98371 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq98329 eq97046
    | exact resolve eq97046 eq98329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97046 eq98329
  have eq98514 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq98371 eq21252
    | exact resolve eq21252 eq98371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21252 eq98371
  have eq98538 : y = (M.op y y) := by
    first
    | (have r₁ := eq98514
       have r₂ := eq27
       grind)
    | exact resolve eq98514 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98514
  have eq104762 : y = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq97173
       have i₂ := eq98538
       grind)
    | exact superpose eq98538 eq97173
    | exact resolve eq97173 eq98538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97173 eq98538
  have eq104797 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 y
       have i₂ := eq104762
       grind)
    | exact superpose eq104762 eq54
    | exact resolve eq54 eq104762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq104762
  have eq104810 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq104797 X0 x
       have i₂ := eq12404 X0 x
       grind)
    | exact superpose eq12404 eq104797
    | exact resolve eq104797 eq12404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12404 eq104797
  have eq105014 : (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq104810 x
       grind)
    | exact superpose eq104810 eq18
    | (have j1 := eq104810 x
       grind)
    | exact resolve eq18 eq104810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104810
  have eq105245 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq105014
       have i₂ := eq96249
       grind)
    | exact superpose eq96249 eq105014
    | exact resolve eq105014 eq96249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96249 eq105014
  have eq105314 : x = (M.op y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12155 eq105245
    | exact resolve eq105245 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105245
  have eq105404 : (M.op x y) = (k x y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq58912 x
       have i₂ := eq105314
       grind)
    | exact superpose eq105314 eq58912
    | exact resolve eq58912 eq105314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58912 eq105314
  have eq105426 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq105404
       have i₂ := eq18800
       grind)
    | exact superpose eq18800 eq105404
    | exact resolve eq105404 eq18800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18800 eq105404
  have eq105436 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq105426
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105426
    | exact resolve eq105426 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq105426
  have eq105445 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12155 eq105436
    | exact resolve eq105436 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12155 eq105436
  have eq105446 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq105445
  have eq105495 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105446 eq15
    | exact resolve eq15 eq105446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105446
  have eq105598 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq105495
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq105495
    | exact resolve eq105495 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq105495
  have eq105619 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12420 eq105598
    | exact resolve eq105598 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12420 eq105598
  have eq105630 : False := by grind
  exact eq105630
