import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation828`: `x = x ◇ ((x ◇ y) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation828 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law828 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law828.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq250 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq16
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1040 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq260 (τ X1) (τ X0)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq260
    | (have j0 := eq260 (τ X1) (τ X0)
       grind)
    | exact resolve eq260 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1040 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1040
    | (have j0 := eq1040 X0 X1
       grind)
    | exact resolve eq1040 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1072 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1062 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1062
    | (have j0 := eq1062 X0 X1
       grind)
    | exact resolve eq1062 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1081 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1072 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1072
    | (have j0 := eq1072 X0 X1
       grind)
    | exact resolve eq1072 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1089 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1081 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1081
    | (have j0 := eq1081 X0 X1
       grind)
    | exact resolve eq1081 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1095 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1089 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1089
    | (have j0 := eq1089 X0 X1
       grind)
    | exact resolve eq1089 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1098 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1095 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1095
    | (have j0 := eq1095 X0 X1
       grind)
    | exact resolve eq1095 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1133 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq261 (τ X1) (τ X0)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq261
    | (have j0 := eq261 (τ X1) (τ X0)
       grind)
    | exact resolve eq261 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1157 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1133 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1133
    | (have j0 := eq1133 X0 X1
       grind)
    | exact resolve eq1133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1167 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1157 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1157
    | (have j0 := eq1157 X0 X1
       grind)
    | exact resolve eq1157 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1176 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1167 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1167
    | (have j0 := eq1167 X0 X1
       grind)
    | exact resolve eq1167 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1184 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1176 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1176
    | (have j0 := eq1176 X0 X1
       grind)
    | exact resolve eq1176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1190 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1184 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1184
    | (have j0 := eq1184 X0 X1
       grind)
    | exact resolve eq1184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1193 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1190 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1190
    | (have j0 := eq1190 X0 X1
       grind)
    | exact resolve eq1190 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq3336 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq76
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq3398 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3336 X0 X1
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq3336
    | (have j0 := eq3336 X0 X1
       grind)
    | exact resolve eq3336 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336
  have eq3406 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq3398 X0 X1
       grind)
    | exact superpose eq3398 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq3398 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq3398 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq3398 X0 X0
       grind)
    | exact resolve eq13 eq3398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3455 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3398 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398
  have eq3457 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3406 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406
  have eq3460 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3457 X0 X1
       have j1 := eq3455 X0 X1
       grind)
    | (have r₁ := eq3457 X0 X1
       have r₂ := eq3455 (k X1 X0) X1
       grind)
    | (have r₁ := eq3457 X0 X0
       have r₂ := eq3455 X0 (k X0 X0)
       grind)
    | (have r₁ := eq3457 X0 X1
       have r₂ := eq3455 X0 X1
       grind)
    | exact resolve eq3457 eq3455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3457
  have eq3701 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3455 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3455
  have eq3706 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq3701 X0
       grind)
    | exact superpose eq3701 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq3701 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3701 X0
       grind)
    | exact resolve eq12 eq3701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3701
  have eq3738 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3706 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3706
  have eq4001 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3738 X0
       grind)
    | exact superpose eq3738 eq11
    | (have j1 := eq3738 X0
       grind)
    | exact resolve eq11 eq3738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3738
  have eq4109 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4001 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4001
    | (have j0 := eq4001 X0
       grind)
    | exact resolve eq4001 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4001
  have eq4127 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4109 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq4109
    | exact resolve eq4109 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4172 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq4109 (τ X0)
       grind)
    | exact superpose eq4109 eq17
    | (have j1 := eq4109 (τ X0)
       grind)
    | exact resolve eq17 eq4109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4109
  have eq4228 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq4172 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4172
    | (have j0 := eq4172 X0
       grind)
    | exact resolve eq4172 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4172
  have eq4278 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4228 X0
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq4228
    | (have j0 := eq4228 X0
       grind)
    | exact resolve eq4228 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq4228
  have eq7009 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (τ (k (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq4278 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4278
    | exact resolve eq4278 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278
  have eq7080 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (τ (k (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7009 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq7009
    | (have j0 := eq7009 X0
       grind)
    | exact resolve eq7009 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7009
  have eq7086 : ∀ X0 : G, (k (τ (σ X0)) X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7080 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq7080
    | (have j0 := eq7080 X0
       grind)
    | exact resolve eq7080 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq7080
  have eq7088 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7086 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7086
    | (have j0 := eq7086 X0
       grind)
    | exact resolve eq7086 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7086
  have eq7100 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1193 X0 X0
       have i₂ := eq7088 X0
       grind)
    | exact superpose eq7088 eq1193
    | (have j0 := eq1193 X0 X0
       have j1 := eq7088 X0
       grind)
    | (have r₁ := eq1193 X0 X0
       have r₂ := eq7088 X0
       grind)
    | exact resolve eq1193 eq7088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7088
  have eq7169 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7100 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7100
  have eq7170 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7169 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7169
  have eq7536 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq7170 X0
       grind)
    | exact superpose eq7170 eq10
    | (have j1 := eq7170 X0
       grind)
    | exact resolve eq10 eq7170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7170
  have eq7598 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7536 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq7536
    | (have j0 := eq7536 X0
       grind)
    | exact resolve eq7536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7536
  have eq7695 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7598 (σ X0)
       grind)
    | exact superpose eq7598 eq15
    | (have j1 := eq7598 (σ X0)
       grind)
    | exact resolve eq15 eq7598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7598
  have eq30584 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7695 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7695
  have eq30592 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq30584 X0
       have j1 := eq4127 X0
       grind)
    | (have r₁ := eq30584 X0
       have r₂ := eq4127 X0
       grind)
    | exact resolve eq30584 eq4127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4127 eq30584
  have eq30630 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq30592 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30592
    | exact resolve eq30592 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30829 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq30630 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq30630
    | exact resolve eq30630 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30630
  have eq30854 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq30829 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30829
    | exact resolve eq30829 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30829
  have eq50946 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3460 X0 X1
       grind)
    | exact superpose eq3460 eq11
    | (have j1 := eq3460 X0 X1
       grind)
    | exact resolve eq11 eq3460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3460
  have eq51142 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50946 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq50946
    | (have j0 := eq50946 X0 X1
       grind)
    | exact resolve eq50946 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50946
  have eq51795 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq51142 (τ X0) X1
       grind)
    | exact superpose eq51142 eq18
    | (have j1 := eq51142 (τ X0) X1
       grind)
    | exact resolve eq18 eq51142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51142
  have eq356994 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (M.op (τ X1) X0) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq51795 X1 X0
       grind)
    | exact superpose eq51795 eq18
    | (have j1 := eq51795 X1 X0
       grind)
    | exact resolve eq18 eq51795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq51795
  have eq600923 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (τ (σ X1)) X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq356994 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq356994
    | (have j0 := eq356994 X0 (σ X1)
       grind)
    | exact resolve eq356994 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356994
  have eq601502 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq600923 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq600923
    | (have j0 := eq600923 X0 X1
       grind)
    | exact resolve eq600923 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600923
  have eq601713 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq601502 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq601502
    | (have j0 := eq601502 X0 X1
       grind)
    | exact resolve eq601502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601502
  have eq603430 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq250
       have i₂ := eq601713 y x
       grind)
    | exact superpose eq601713 eq250
    | (have j1 := eq601713 y x
       grind)
    | (have r₁ := eq250
       have r₂ := eq601713 y x
       grind)
    | exact resolve eq250 eq601713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq601713
  have eq603933 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq603430
  have eq604067 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq261 x y
       grind)
    | (have r₁ := eq603933
       have r₂ := eq261 x y
       grind)
    | exact resolve eq603933 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq603933
  have eq608065 : y ≠ y ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq604067
       grind)
    | exact superpose eq604067 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq604067
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq604067
       grind)
    | exact resolve eq12 eq604067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604067
  have eq608157 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq608065
  have eq608914 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq260 x y
       have i₂ := eq608157
       grind)
    | exact superpose eq608157 eq260
    | (have j0 := eq260 x y
       grind)
    | exact resolve eq260 eq608157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq608157
  have eq609021 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq608914
  have eq609022 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq609021
  have eq609036 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq609022
       grind)
    | exact superpose eq609022 eq16
    | exact resolve eq16 eq609022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609140 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq609022
       grind)
    | exact superpose eq609022 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq609022
       grind)
    | exact resolve eq12 eq609022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609022
  have eq609233 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq609140
  have eq609281 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq609233
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq609233
    | exact resolve eq609233 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609233
  have eq610915 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq609281
       grind)
    | exact superpose eq609281 eq16
    | exact resolve eq16 eq609281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611019 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq609281
       grind)
    | exact superpose eq609281 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq609281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611020 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq609281
       grind)
    | exact superpose eq609281 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq609281
       grind)
    | exact resolve eq13 eq609281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609281
  have eq611113 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq611020
  have eq611126 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq611113
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq611113
    | exact resolve eq611113 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611113
  have eq611127 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq611019
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq611019
    | exact resolve eq611019 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611019
  have eq611128 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq611127
  have eq614766 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq611128
       have i₂ := eq611126
       grind)
    | exact superpose eq611126 eq611128
    | (have r₁ := eq611128
       have r₂ := eq611126
       grind)
    | exact resolve eq611128 eq611126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611126
  have eq615278 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq614766
  have eq615279 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq615278
  have eq615466 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq615279
       grind)
    | exact superpose eq615279 eq10
    | exact resolve eq10 eq615279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615279
  have eq616109 : y = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq615466
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq615466
    | exact resolve eq615466 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615466
  have eq617247 : y ≠ y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq1193 y x
       have i₂ := eq616109
       grind)
    | exact superpose eq616109 eq1193
    | (have j0 := eq1193 y x
       grind)
    | (have r₁ := eq1193 y x
       have r₂ := eq616109
       grind)
    | exact resolve eq1193 eq616109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq617307 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq617247
  have eq617359 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq617307
       grind)
    | exact superpose eq617307 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq617307
       grind)
    | exact resolve eq12 eq617307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617455 : x ≠ y ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq617307
  have eq617456 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq617359
  have eq619875 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq617456
       have i₂ := eq616109
       grind)
    | exact superpose eq616109 eq617456
    | exact resolve eq617456 eq616109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616109 eq617456
  have eq620030 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq619875
       have r₂ := eq617455
       grind)
    | exact resolve eq619875 eq617455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617455 eq619875
  have eq620032 : x = (M.op x y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq620030
       have r₂ := eq611128
       grind)
    | exact resolve eq620030 eq611128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611128 eq620030
  have eq620043 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq610915
       have i₂ := eq620032
       grind)
    | exact superpose eq620032 eq610915
    | exact resolve eq610915 eq620032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610915 eq620032
  have eq620147 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq620043
  have eq620148 : (σ x) = (σ (k y x)) := by grind
  clear eq620147
  have eq622288 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq620148
       grind)
    | exact superpose eq620148 eq10
    | exact resolve eq10 eq620148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622939 : x = (k y x) := by
    first
    | (have i₁ := eq622288
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq622288
    | exact resolve eq622288 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622288
  have eq623223 : x ≠ x ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1098 y x
       have i₂ := eq622939
       grind)
    | exact superpose eq622939 eq1098
    | (have j0 := eq1098 y x
       grind)
    | (have r₁ := eq1098 y x
       have r₂ := eq622939
       grind)
    | exact resolve eq1098 eq622939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq623288 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq623223
  have eq623909 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq609036
       have i₂ := eq623288
       grind)
    | exact superpose eq623288 eq609036
    | exact resolve eq609036 eq623288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609036 eq623288
  have eq624013 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq623909
  have eq638738 : x ≠ x ∨ y = (k y x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq624013
       grind)
    | exact superpose eq624013 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq624013
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq624013
       grind)
    | exact resolve eq13 eq624013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624013
  have eq638840 : y = (k y x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq638738
  have eq638851 : x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq638840
       have i₂ := eq622939
       grind)
    | exact superpose eq622939 eq638840
    | exact resolve eq638840 eq622939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622939 eq638840
  have eq638852 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq638851
  have eq638853 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq638852
       grind)
    | exact superpose eq638852 eq16
    | exact resolve eq16 eq638852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638852
  have eq638926 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq638853
       have i₂ := eq30592 x
       grind)
    | exact superpose eq30592 eq638853
    | exact resolve eq638853 eq30592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638853
  have eq638933 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq638926
       have i₂ := eq30854 x
       grind)
    | exact superpose eq30854 eq638926
    | exact resolve eq638926 eq30854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638926
  have eq638934 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq638933
  have eq640105 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq638934
       grind)
    | exact superpose eq638934 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq638934
       grind)
    | exact resolve eq13 eq638934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640207 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq640105
  have eq640219 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq640207
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq640207
    | exact resolve eq640207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640207
  have eq640257 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq640219
       have i₂ := eq620148
       grind)
    | exact superpose eq620148 eq640219
    | exact resolve eq640219 eq620148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620148 eq640219
  have eq640258 : (σ x) = (σ y) := by grind
  clear eq640257
  have eq640349 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq638934
       have i₂ := eq640258
       grind)
    | exact superpose eq640258 eq638934
    | exact resolve eq638934 eq640258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638934
  have eq640350 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq640258
       grind)
    | exact superpose eq640258 eq10
    | exact resolve eq10 eq640258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640258
  have eq641013 : x = y := by
    first
    | (have i₁ := eq640350
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq640350
    | exact resolve eq640350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640350
  have eq641014 : (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq640349
       have i₂ := eq30592 x
       grind)
    | exact superpose eq30592 eq640349
    | exact resolve eq640349 eq30592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640349
  have eq641134 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq641014
       have i₂ := eq30854 x
       grind)
    | exact superpose eq30854 eq641014
    | exact resolve eq641014 eq30854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641014
  have eq642721 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq641013
       grind)
    | exact superpose eq641013 eq16
    | exact resolve eq16 eq641013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641013
  have eq642797 : (σ (k x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq642721
       have i₂ := eq30592 x
       grind)
    | exact superpose eq30592 eq642721
    | exact resolve eq642721 eq30592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30592 eq642721
  have eq642807 : (σ x) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq642797
       have i₂ := eq641134
       grind)
    | exact superpose eq641134 eq642797
    | exact resolve eq642797 eq641134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642797
  have eq642813 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq642807
       have i₂ := eq30854 x
       grind)
    | exact superpose eq30854 eq642807
    | exact resolve eq642807 eq30854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30854 eq642807
  have eq642816 : False := by grind
  exact eq642816

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq88 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq119 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51
    | exact resolve eq51 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq130 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq119
    | (have j0 := eq119 X0
       grind)
    | exact resolve eq119 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq119
  have eq132 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq130 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq130
    | (have j0 := eq130 X0
       grind)
    | exact resolve eq130 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq133 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq132 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq132 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq132 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq136 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq133 (σ X0)
       grind)
    | exact superpose eq133 eq15
    | exact resolve eq15 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq136 X0
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq136
    | exact resolve eq136 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq136
  have eq333 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86 x y
       grind)
    | exact superpose eq86 eq16
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1293 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq88
    | exact resolve eq88 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1351 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1293 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1293
    | (have j0 := eq1293 X0 X1
       grind)
    | exact resolve eq1293 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq2138 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq333
       have i₂ := eq1351 x y
       grind)
    | exact superpose eq1351 eq333
    | (have j1 := eq1351 (σ x) (σ y)
       grind)
    | (have r₁ := eq333
       have r₂ := eq1351 x y
       grind)
    | (have r₁ := eq333
       have r₂ := eq1351 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq333
       have r₂ := eq1351 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq333 eq1351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2139 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq2138
  have eq33657 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2139
       grind)
    | exact superpose eq2139 eq16
    | exact resolve eq16 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139
  have eq33658 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq33657
       have r₂ := eq149 x
       grind)
    | exact resolve eq33657 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33657
  have eq33661 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq33658
       grind)
    | exact superpose eq33658 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq33658
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq33658
       grind)
    | exact resolve eq12 eq33658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33658
  have eq33726 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq33661
  have eq34272 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq333
       have i₂ := eq33726
       grind)
    | exact superpose eq33726 eq333
    | exact resolve eq333 eq33726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq33726
  have eq34309 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq34272
  have eq34310 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq34309
  have eq34752 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq34310
       grind)
    | exact superpose eq34310 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq34310
       grind)
    | exact resolve eq12 eq34310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34310
  have eq34817 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq34752
  have eq34844 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34817
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq34817
    | exact resolve eq34817 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34817
  have eq38303 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34844
       grind)
    | exact superpose eq34844 eq16
    | exact resolve eq16 eq34844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34844
  have eq38439 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq38303
       have i₂ := eq1351 x y
       grind)
    | exact superpose eq1351 eq38303
    | (have j1 := eq1351 x y
       grind)
    | (have r₁ := eq38303
       have r₂ := eq1351 x y
       grind)
    | (have r₁ := eq38303
       have r₂ := eq1351 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq38303
       have r₂ := eq1351 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq38303 eq1351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351
  have eq38440 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq38439
  have eq38876 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38440
       grind)
    | exact superpose eq38440 eq16
    | exact resolve eq16 eq38440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38440
  have eq38888 : y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq38876
       have r₂ := eq149 x
       grind)
    | exact resolve eq38876 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38876
  have eq38891 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq38888
       grind)
    | exact superpose eq38888 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq38888
       grind)
    | exact resolve eq12 eq38888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38888
  have eq38956 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq38891
  have eq39418 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38303
       have i₂ := eq38956
       grind)
    | exact superpose eq38956 eq38303
    | exact resolve eq38303 eq38956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38303 eq38956
  have eq39458 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq39418
  have eq39459 : (σ x) = (σ y) := by grind
  clear eq39458
  have eq39812 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39459
       grind)
    | exact superpose eq39459 eq16
    | exact resolve eq16 eq39459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39813 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq39459
       grind)
    | exact superpose eq39459 eq10
    | exact resolve eq10 eq39459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39459
  have eq39957 : x = y := by
    first
    | (have i₁ := eq39813
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq39813
    | exact resolve eq39813 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39813
  have eq39958 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq39812
       have i₂ := eq149 x
       grind)
    | exact superpose eq149 eq39812
    | exact resolve eq39812 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq39812
  have eq39965 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq39958
       have i₂ := eq39957
       grind)
    | exact superpose eq39957 eq39958
    | exact resolve eq39958 eq39957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39957 eq39958
  have eq39966 : False := by grind
  exact eq39966

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq77 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq180 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq77 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq187 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq188 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq187 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq194 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       have j1 := eq186 X0 X1
       grind)
    | (have r₁ := eq190 X0 X1
       have r₂ := eq186 X0 X1
       grind)
    | (have r₁ := eq190 (k X0 X1) X0
       have r₂ := eq186 X0 X1
       grind)
    | (have r₁ := eq190 X0 X0
       have r₂ := eq186 X0 X0
       grind)
    | exact resolve eq190 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq190
  have eq589 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq194
    | exact resolve eq194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq194 x y
       grind)
    | exact superpose eq194 eq16
    | (have j1 := eq194 x y
       grind)
    | exact resolve eq16 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq618 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq589 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq589
    | (have j0 := eq589 X0 X1
       grind)
    | exact resolve eq589 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq589
  have eq620 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq618 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq618
    | exact resolve eq618 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq679 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq620 (τ X0) X1
       grind)
    | exact superpose eq620 eq18
    | (have j1 := eq620 (τ X0) X1
       grind)
    | exact resolve eq18 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq620
  have eq959 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq679 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq679
    | exact resolve eq679 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq1014 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq959 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq959
    | (have j0 := eq959 X0 X1
       grind)
    | exact resolve eq959 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq1123 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq597
       have i₂ := eq1014 x y
       grind)
    | exact superpose eq1014 eq597
    | (have j1 := eq1014 (σ x) (σ y)
       grind)
    | (have r₁ := eq597
       have r₂ := eq1014 x y
       grind)
    | exact resolve eq597 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1124 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1123
  have eq1187 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1124
  have eq1207 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq597
       have i₂ := eq1187
       grind)
    | exact superpose eq1187 eq597
    | exact resolve eq597 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq1187
  have eq1208 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1207
  have eq1209 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1208
  have eq1225 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1209
  have eq1246 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1225
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1225
    | exact resolve eq1225 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1252 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1246
       grind)
    | exact superpose eq1246 eq16
    | exact resolve eq16 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1318 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1252
       have i₂ := eq1014 x y
       grind)
    | exact superpose eq1014 eq1252
    | (have j1 := eq1014 x y
       grind)
    | (have r₁ := eq1252
       have r₂ := eq1014 x y
       grind)
    | exact resolve eq1252 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1319 : x = (M.op y y) := by grind
  clear eq1318
  have eq1328 : (M.op x y) = (k x y) := by grind
  clear eq1319
  have eq1354 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1252
       have i₂ := eq1328
       grind)
    | exact superpose eq1328 eq1252
    | exact resolve eq1252 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252 eq1328
  have eq1357 : False := by grind
  exact eq1357

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_x_pyx_pxx_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op y (M.op (M.op x y) (M.op X0 y))) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  have eq66 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
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
  clear eq68 eq71
  have eq79 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq22 eq36
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq102
    | (have j1 := eq79 y x
       grind)
    | exact resolve eq102 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq126 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (k y x) = (M.op y y) := by
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
  have eq127 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq119 eq79
    | (have j0 := eq79 (σ y) (σ x)
       grind)
    | exact resolve eq79 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq140
    | exact resolve eq140 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq144 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq141
       have r₂ := eq27
       grind)
    | exact resolve eq141 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq146 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq144
    | exact resolve eq144 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq165 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq146 eq27
    | exact resolve eq27 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : y = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq265 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq146 eq51
    | exact resolve eq51 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq276 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq265
    | (have j0 := eq265 (σ x)
       grind)
    | exact resolve eq265 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq146 eq276
    | exact resolve eq276 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq286 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq281
  have eq287 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq286 eq265
    | exact resolve eq265 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq286
  have eq292 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq287
  have eq485 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq146 eq127
    | (have r₁ := eq127
       have r₂ := eq146
       grind)
    | exact resolve eq127 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq486 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq485
  have eq489 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq486 eq119
    | exact resolve eq119 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq492 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq489
  have eq500 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq492 eq73
    | exact resolve eq73 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq492
  have eq507 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq500
    | exact resolve eq500 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq500
  have eq516 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq507 eq292
    | exact resolve eq292 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292 eq507
  have eq534 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq516
  have eq539 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq534
       have r₂ := eq165
       grind)
    | exact resolve eq534 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq534
  have eq542 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq539
       grind)
    | exact superpose eq539 eq74
    | exact resolve eq74 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq539
  have eq550 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq542
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq542
    | exact resolve eq542 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq602 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq550 eq66
    | exact resolve eq66 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq550
  have eq612 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq602
       have r₂ := eq146
       grind)
    | exact resolve eq602 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq602
  have eq617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq612 eq119
    | exact resolve eq119 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq612
  have eq620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq617
  have eq624 : y = (M.op x y) := by
    first
    | (have r₁ := eq620
       have r₂ := eq27
       grind)
    | exact resolve eq620 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq626 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq624 eq20
    | exact resolve eq20 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq628 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq624 eq50
    | exact resolve eq50 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq631 : y ≠ y ∨ y = (M.op x x) ∨ (k y x) = (M.op y y) := by
    first
    | exact superpose eq624 eq126
    | (have r₁ := eq126
       have r₂ := eq624
       grind)
    | exact resolve eq126 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq635 : y = (M.op y (M.op y y)) := by
    first
    | exact superpose eq624 eq252
    | exact resolve eq252 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq636 : y = (M.op x x) ∨ (k y x) = (M.op y y) := by grind
  clear eq631
  have eq642 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq626
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq626
    | exact resolve eq626 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq645 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq642 eq26
    | exact resolve eq26 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq947 : y = (M.op y y) := by
    first
    | (have i₁ := eq628 y
       have i₂ := eq635
       grind)
    | exact superpose eq635 eq628
    | exact resolve eq628 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq635
  have eq1349 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq636
       have i₂ := eq947
       grind)
    | exact superpose eq947 eq636
    | exact resolve eq636 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636 eq947
  have eq1353 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq1349
       grind)
    | exact superpose eq1349 eq102
    | exact resolve eq102 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1360 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq642 eq1353
    | exact resolve eq1353 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq1362 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1360
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1360
    | exact resolve eq1360 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq1363 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq642 eq1362
    | exact resolve eq1362 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq1366 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1363 eq79
    | (have j0 := eq79 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq79 eq1363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq1367 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq1366
  have eq1369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq645 eq1367
    | exact resolve eq1367 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq1372 : y = (M.op x x) := by
    first
    | (have r₁ := eq1369
       have r₂ := eq27
       grind)
    | exact resolve eq1369 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1376 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq65
       have i₂ := eq1372
       grind)
    | exact superpose eq1372 eq65
    | exact resolve eq65 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1372
  have eq1392 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq1376
       have r₂ := eq624
       grind)
    | exact resolve eq1376 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq1394 : y = (k y x) := by
    first
    | exact superpose eq624 eq1392
    | exact resolve eq1392 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624 eq1392
  have eq1419 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq102
       have i₂ := eq1394
       grind)
    | exact superpose eq1394 eq102
    | exact resolve eq102 eq1394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq1394
  have eq1426 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq642 eq1419
    | exact resolve eq1419 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq1428 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1426
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1426
    | exact resolve eq1426 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1426
  have eq1429 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq642 eq1428
    | exact resolve eq1428 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq1428
  have eq1432 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1429 eq79
    | (have j0 := eq79 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq79 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq1429
  have eq1433 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1432
  have eq1435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq645 eq1433
    | exact resolve eq1433 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq1433
  have eq1438 : False := by grind
  exact eq1438

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pyx_pyy_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq93 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq449 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq479 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq449 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq449
    | (have j0 := eq449 X0 X1
       grind)
    | exact resolve eq449 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq449
  have eq484 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq479 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq479 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq479 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq479 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq487 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq484
    | (have j0 := eq484 X0 X1
       grind)
    | exact resolve eq484 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq484
  have eq574 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq487 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq487
    | exact resolve eq487 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq487 (σ X0) X1
       grind)
    | exact superpose eq487 eq15
    | (have j1 := eq487 (σ X0) X1
       grind)
    | exact resolve eq15 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq605 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq581 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq581
    | (have j0 := eq581 X0 X1
       grind)
    | exact resolve eq581 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq622 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq574 X1 (σ X0)
       grind)
    | exact superpose eq574 eq24
    | (have j1 := eq574 X1 (σ X0)
       grind)
    | exact resolve eq24 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq634 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq574 (τ X1) X0
       grind)
    | exact superpose eq574 eq17
    | (have j1 := eq574 (τ X1) X0
       grind)
    | exact resolve eq17 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq574
  have eq645 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq622 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq622
    | (have j0 := eq622 X0 X1
       grind)
    | exact resolve eq622 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq1265 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq634 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq634
    | exact resolve eq634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq1318 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1265 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1265
    | (have j0 := eq1265 X0 X1
       grind)
    | exact resolve eq1265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq5936 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq605 x y
       grind)
    | exact superpose eq605 eq16
    | (have j1 := eq605 x y
       grind)
    | exact resolve eq16 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6000 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq605 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq6225 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq5936
       have i₂ := eq1318 y x
       grind)
    | exact superpose eq1318 eq5936
    | (have j1 := eq1318 y x
       grind)
    | (have r₁ := eq5936
       have r₂ := eq1318 y x
       grind)
    | exact resolve eq5936 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5936
  have eq6226 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6225
  have eq6231 : y ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq6226
       grind)
    | exact superpose eq6226 eq12
    | exact resolve eq12 eq6226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6232 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq6226
       grind)
    | exact superpose eq6226 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6226
       grind)
    | exact resolve eq13 eq6226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6226
  have eq6253 : (k y x) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6232
  have eq6254 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6231
       have r₂ := eq6253
       grind)
    | exact resolve eq6231 eq6253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6231 eq6253
  have eq6330 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq471 x y
       have i₂ := eq6254
       grind)
    | exact superpose eq6254 eq471
    | (have j0 := eq471 x y
       grind)
    | exact resolve eq471 eq6254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq6340 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6330
  have eq6341 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6340
  have eq6359 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq645 x (σ y)
       have i₂ := eq6341
       grind)
    | exact superpose eq6341 eq645
    | (have j0 := eq645 x (σ y)
       grind)
    | exact resolve eq645 eq6341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq6373 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq6341
       grind)
    | exact superpose eq6341 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq6341
       grind)
    | exact resolve eq12 eq6341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6396 : (σ y) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6341
  have eq6397 : (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6373
  have eq6400 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq6397
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6397
    | exact resolve eq6397 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6397
  have eq6402 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6359
       have r₂ := eq6396
       grind)
    | exact resolve eq6359 eq6396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6359
  have eq6406 : y = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6402
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6402
    | exact resolve eq6402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6402
  have eq6475 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6254
       have i₂ := eq6406
       grind)
    | exact superpose eq6406 eq6254
    | exact resolve eq6254 eq6406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6406
  have eq6509 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq6475
  have eq6529 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq6509
       grind)
    | exact superpose eq6509 eq12
    | exact resolve eq12 eq6509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6530 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq6509
       grind)
    | exact superpose eq6509 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq6509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6509
  have eq6557 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq6530
       have r₂ := eq67 x
       grind)
    | exact resolve eq6530 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6530
  have eq6558 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6529
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6529
    | exact resolve eq6529 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6529
  have eq6559 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6557
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6557
    | exact resolve eq6557 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6557
  have eq6560 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6559
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq6559
    | exact resolve eq6559 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6559
  have eq6561 : y = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6560
       have r₂ := eq6558
       grind)
    | exact resolve eq6560 eq6558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6558 eq6560
  have eq6760 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6396
       have i₂ := eq6561
       grind)
    | exact superpose eq6561 eq6396
    | exact resolve eq6396 eq6561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6396 eq6561
  have eq6761 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq6760
  have eq6850 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq6400
       grind)
    | exact superpose eq6400 eq12
    | exact resolve eq12 eq6400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6851 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq6400
       grind)
    | exact superpose eq6400 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq6400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6400
  have eq6884 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq6851
       have r₂ := eq67 x
       grind)
    | exact resolve eq6851 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6851
  have eq6885 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq6850
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6850
    | exact resolve eq6850 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6850
  have eq6886 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq6884
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6884
    | exact resolve eq6884 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6884
  have eq6887 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq6886
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq6886
    | exact resolve eq6886 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq6886
  have eq6888 : (σ y) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6887
       have r₂ := eq6885
       grind)
    | exact resolve eq6887 eq6885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6885 eq6887
  have eq7020 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq6888
  have eq7589 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6000 x y
       have i₂ := eq6254
       grind)
    | exact superpose eq6254 eq6000
    | (have j0 := eq6000 x y
       grind)
    | exact resolve eq6000 eq6254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6000 eq6254
  have eq7615 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7589
  have eq7616 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7615
  have eq7831 : (σ y) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6761
       have i₂ := eq7616
       grind)
    | exact superpose eq7616 eq6761
    | exact resolve eq6761 eq7616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6761
  have eq7832 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7616
       grind)
    | exact superpose eq7616 eq16
    | exact resolve eq16 eq7616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7616
  have eq7892 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq7831
       have r₂ := eq7020
       grind)
    | exact resolve eq7831 eq7020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7020 eq7831
  have eq8054 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1318 y x
       have i₂ := eq7892
       grind)
    | exact superpose eq7892 eq1318
    | (have j0 := eq1318 y x
       grind)
    | exact resolve eq1318 eq7892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318 eq7892
  have eq8116 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq8054
       have r₂ := eq7832
       grind)
    | exact resolve eq8054 eq7832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8054
  have eq8296 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7832
       have i₂ := eq8116
       grind)
    | exact superpose eq8116 eq7832
    | exact resolve eq7832 eq8116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7832 eq8116
  have eq8346 : False := by grind
  exact eq8346

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq75 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq76 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq151 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq154 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq499 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq76 X0 (M.op x X0)
       have i₂ := eq75 X0 x
       grind)
    | exact superpose eq75 eq76
    | (have j0 := eq76 X0 x
       have j1 := eq75 X0 x
       grind)
    | exact resolve eq76 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq76
  have eq507 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq499 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq508 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq507 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq507 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq507 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq519 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq508 (σ X0)
       grind)
    | exact superpose eq508 eq15
    | exact resolve eq15 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq519 X0
       have i₂ := eq508 X0
       grind)
    | exact superpose eq508 eq519
    | exact resolve eq519 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq519
  have eq2717 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq151 x y
       grind)
    | exact superpose eq151 eq16
    | (have j1 := eq151 x y
       grind)
    | exact resolve eq16 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2747 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq2979 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq154 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq154
    | exact resolve eq154 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq3043 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2979 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2979
    | (have j0 := eq2979 X0 X1
       grind)
    | exact resolve eq2979 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2979
  have eq3183 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2747 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq2747
    | (have j0 := eq2747 (τ X0) (τ X1)
       grind)
    | exact resolve eq2747 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq3218 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3183 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3183
    | (have j0 := eq3183 X0 X1
       grind)
    | exact resolve eq3183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3183
  have eq3235 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3218 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3218
    | (have j0 := eq3218 X0 X1
       grind)
    | exact resolve eq3218 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3218
  have eq3251 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3235 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3235
    | (have j0 := eq3235 X0 X1
       grind)
    | exact resolve eq3235 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3235
  have eq3252 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3251 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3251
    | (have j0 := eq3251 X0 X1
       grind)
    | exact resolve eq3251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3251
  have eq3253 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ X0 = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3252 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3252
    | (have j0 := eq3252 X0 X1
       grind)
    | exact resolve eq3252 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3252
  have eq3254 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3253 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3253
    | (have j0 := eq3253 X0 X1
       grind)
    | exact resolve eq3253 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3253
  have eq16293 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2717
       have i₂ := eq3043 y x
       grind)
    | exact superpose eq3043 eq2717
    | (have j1 := eq3043 (σ x) (σ y)
       grind)
    | (have r₁ := eq2717
       have r₂ := eq3043 y x
       grind)
    | (have r₁ := eq2717
       have r₂ := eq3043 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2717
       have r₂ := eq3043 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2717 eq3043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717 eq3043
  have eq16294 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq16293
  have eq16296 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16294
       grind)
    | exact superpose eq16294 eq16
    | exact resolve eq16 eq16294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16294
  have eq16297 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16296
       have r₂ := eq538 x
       grind)
    | exact resolve eq16296 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16296
  have eq16300 : x ≠ x ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq16297
       grind)
    | exact superpose eq16297 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq16297
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16297
       grind)
    | exact resolve eq12 eq16297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16297
  have eq16325 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16300
  have eq16329 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2747 x y
       have i₂ := eq16325
       grind)
    | exact superpose eq16325 eq2747
    | (have j0 := eq2747 x y
       grind)
    | exact resolve eq2747 eq16325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2747 eq16325
  have eq16350 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16329
  have eq16351 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq16350
  have eq16357 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16351
       grind)
    | exact superpose eq16351 eq16
    | exact resolve eq16 eq16351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16368 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq16351
       grind)
    | exact superpose eq16351 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16351
       grind)
    | exact resolve eq12 eq16351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16351
  have eq16393 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq16368
  have eq16407 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16393
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq16393
    | exact resolve eq16393 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16393
  have eq16413 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16407
       grind)
    | exact superpose eq16407 eq10
    | exact resolve eq10 eq16407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16407
  have eq16486 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16413
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16413
    | exact resolve eq16413 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16413
  have eq16491 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16486
       grind)
    | exact superpose eq16486 eq16
    | exact resolve eq16 eq16486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16486
  have eq16492 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq16491
       have r₂ := eq538 x
       grind)
    | exact resolve eq16491 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16491
  have eq16502 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq16492
       grind)
    | exact superpose eq16492 eq10
    | exact resolve eq10 eq16492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16492
  have eq16576 : x = (k y x) := by
    first
    | (have i₁ := eq16502
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16502
    | exact resolve eq16502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16502
  have eq16590 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3254 y x
       have i₂ := eq16576
       grind)
    | exact superpose eq16576 eq3254
    | (have j0 := eq3254 x y
       grind)
    | (have r₁ := eq3254 y x
       have r₂ := eq16576
       grind)
    | exact resolve eq3254 eq16576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3254 eq16576
  have eq16604 : x = y ∨ x = (M.op x y) := by grind
  clear eq16590
  have eq16608 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16604
       grind)
    | exact superpose eq16604 eq16
    | exact resolve eq16 eq16604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16604
  have eq16613 : x = (M.op x y) := by
    first
    | (have r₁ := eq16608
       have r₂ := eq538 x
       grind)
    | exact resolve eq16608 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16608
  have eq16617 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16357
       have i₂ := eq16613
       grind)
    | exact superpose eq16613 eq16357
    | exact resolve eq16357 eq16613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16357 eq16613
  have eq16646 : (σ x) = (σ y) := by grind
  clear eq16617
  have eq16648 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16646
       grind)
    | exact superpose eq16646 eq10
    | exact resolve eq10 eq16646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16646
  have eq16721 : x = y := by
    first
    | (have i₁ := eq16648
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16648
    | exact resolve eq16648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16648
  have eq16726 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16721
       grind)
    | exact superpose eq16721 eq16
    | exact resolve eq16 eq16721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16721
  have eq16732 : False := by grind
  exact eq16732

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_x_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq35
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq61 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq84 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61 x y
       grind)
    | exact superpose eq61 eq16
    | (have j1 := eq61 x y
       grind)
    | exact resolve eq16 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq875 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq135
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq135
    | (have j1 := eq14 (M.op (σ x) (σ y)) (σ (M.op y y))
       grind)
    | (have r₁ := eq135
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq135
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq135 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq876 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq875
  have eq7380 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq876
       grind)
    | exact superpose eq876 eq16
    | exact resolve eq16 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq7381 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq7380
       have r₂ := eq40 x
       grind)
    | exact resolve eq7380 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7380
  have eq11495 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq84 y (σ x)
       have i₂ := eq7381
       grind)
    | exact superpose eq7381 eq84
    | (have j0 := eq84 y (σ x)
       grind)
    | (have r₁ := eq84 y (σ x)
       have r₂ := eq7381
       grind)
    | exact resolve eq84 eq7381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq7381
  have eq11496 : (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq11495
  have eq11501 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11496
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq11496
    | exact resolve eq11496 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11496
  have eq11671 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11501
       grind)
    | exact superpose eq11501 eq10
    | exact resolve eq10 eq11501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11501
  have eq11766 : x = y ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11671
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11671
    | exact resolve eq11671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11671
  have eq11927 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11766
       grind)
    | exact superpose eq11766 eq16
    | exact resolve eq16 eq11766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11766
  have eq11928 : (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq11927
       have r₂ := eq40 x
       grind)
    | exact resolve eq11927 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11927
  have eq11934 : (k y x) = (τ (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq11928
       grind)
    | exact superpose eq11928 eq10
    | exact resolve eq10 eq11928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11928
  have eq12036 : (k y x) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11934
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq11934
    | exact resolve eq11934 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11934
  have eq12037 : (k y x) = (M.op y y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq12036
       have r₂ := eq12 y x
       grind)
    | exact resolve eq12036 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12036
  have eq12234 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq137 x y
       have i₂ := eq12037
       grind)
    | exact superpose eq12037 eq137
    | (have j0 := eq137 x y
       grind)
    | exact resolve eq137 eq12037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq12235 : (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq12037
       grind)
    | exact superpose eq12037 eq14
    | (have j0 := eq14 (M.op x y) (M.op y y)
       grind)
    | exact resolve eq14 eq12037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12037
  have eq12236 : x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq12235
  have eq12237 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq12234
  have eq12240 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12236
       grind)
    | exact superpose eq12236 eq16
    | exact resolve eq16 eq12236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12236
  have eq12242 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq12240
       have r₂ := eq40 x
       grind)
    | exact resolve eq12240 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12240
  have eq19396 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12237
       grind)
    | exact superpose eq12237 eq16
    | exact resolve eq16 eq12237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12237
  have eq19407 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19396
       have i₂ := eq12242
       grind)
    | exact superpose eq12242 eq19396
    | exact resolve eq19396 eq12242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12242 eq19396
  have eq19408 : (σ x) = (σ y) := by grind
  clear eq19407
  have eq19411 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19408
       grind)
    | exact superpose eq19408 eq16
    | exact resolve eq16 eq19408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19415 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19408
       grind)
    | exact superpose eq19408 eq10
    | exact resolve eq10 eq19408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19408
  have eq19558 : x = y := by
    first
    | (have i₁ := eq19415
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19415
    | exact resolve eq19415 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19415
  have eq19559 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq19411
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq19411
    | exact resolve eq19411 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq19411
  have eq19565 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq19559
       have i₂ := eq19558
       grind)
    | exact superpose eq19558 eq19559
    | exact resolve eq19559 eq19558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19558 eq19559
  have eq19566 : False := by grind
  exact eq19566

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_x_pxy_x_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  have eq52 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq81 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 X2 X0
       have i₂ := eq14 (σ X0) (k X1 (σ X2))
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 (σ X0) (k X1 (σ X2))
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) (τ X0)
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 X1) (M.op (σ X0) (σ X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (M.op (M.op X1 X1) (M.op (σ X0) (σ X0)))
       have i₂ := eq53 (σ X0) X1
       grind)
    | exact superpose eq53 eq29
    | (have j1 := eq53 (σ X0) X1
       grind)
    | exact resolve eq29 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq138 : ∀ X0 X1 : G, (k X0 (τ (M.op (M.op X1 X1) (M.op (σ X0) (σ X0))))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq133
    | (have j0 := eq133 X0 X1
       grind)
    | exact resolve eq133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq282 : ∀ X0 X1 : G, (k X1 (M.op (σ (k X0 X0)) (M.op X1 X1))) = X1 ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 (σ X0)
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq53
    | (have j0 := eq53 X1 X1
       have j1 := eq79 X0 X0
       grind)
    | exact resolve eq53 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq283 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq79 X0 X0
       grind)
    | (have r₁ := eq12 (σ X1) X1
       have r₂ := eq79 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq293 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq283 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq294 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (M.op (σ (k X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq282 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq298 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq293 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq293 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq293 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq1175 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq82 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1176 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq1175 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1178 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1176 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1176
    | (have j0 := eq1176 X0
       grind)
    | exact resolve eq1176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1182 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1178 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1178
    | exact resolve eq1178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1203 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1182 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1182
    | (have j0 := eq1182 X0
       grind)
    | exact resolve eq1182 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1207 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq1203 X0
       grind)
    | exact superpose eq1203 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq1203 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq1203 X0
       grind)
    | exact resolve eq12 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1223 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1248 : ∀ X0 X1 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq1223 X0 X1
       grind)
    | exact superpose eq1223 eq10
    | (have j1 := eq1223 X0 X1
       grind)
    | exact resolve eq10 eq1223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1287 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1248 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1248
    | (have j0 := eq1248 X0 X0
       grind)
    | exact resolve eq1248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1348 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1287 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq1349 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1348 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq1417 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 (M.op (σ (k X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq294 X0 X2
       grind)
    | exact superpose eq294 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq294 X0 X2
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq294 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq294 X0 X1
       grind)
    | exact resolve eq12 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq1430 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 (M.op (σ (k X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1417 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1443 : ∀ X0 X1 X2 : G, (k X2 (M.op (σ (M.op X0 X0)) (M.op X2 X2))) = X2 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1430 X0 X1 X2
       have i₂ := eq1349 X0
       grind)
    | exact superpose eq1349 eq1430
    | (have j0 := eq1430 X0 X1 X2
       grind)
    | exact resolve eq1430 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1469 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X0 X1
       have i₂ := eq1349 X0
       grind)
    | exact superpose eq1349 eq298
    | (have j0 := eq298 X0 X1
       grind)
    | exact resolve eq298 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq1491 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1349 (σ X0)
       grind)
    | exact superpose eq1349 eq15
    | exact resolve eq15 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1497 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq1349 (τ X0)
       grind)
    | exact superpose eq1349 eq32
    | exact resolve eq32 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1519 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1497 X0
       have i₂ := eq1349 X0
       grind)
    | exact superpose eq1349 eq1497
    | exact resolve eq1497 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq1525 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1491 X0
       have i₂ := eq1349 X0
       grind)
    | exact superpose eq1349 eq1491
    | exact resolve eq1491 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349 eq1491
  have eq1731 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq1525 X0
       grind)
    | exact superpose eq1525 eq9
    | exact resolve eq9 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6095 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (M.op (M.op X1 X1) (σ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 X1
       have i₂ := eq1525 X0
       grind)
    | exact superpose eq1525 eq138
    | exact resolve eq138 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq11779 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ X0)))) ∨ (k (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ X0)))) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1443 X0 (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ X0))) (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443
  have eq11792 : ∀ X0 : G, (k (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ X0)))) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq11779 X0
       have j1 := eq14 (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ X0)))
       grind)
    | (have r₁ := eq11779 X0
       have r₂ := eq14 (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq11779 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11779
  have eq11824 : ∀ X0 : G, (k (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ X0)))) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have j0 := eq11792 X0
       have j1 := eq12 (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ X0)))
       grind)
    | (have r₁ := eq11792 X0
       have r₂ := eq12 (σ X0) x
       grind)
    | exact resolve eq11792 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11792
  have eq11848 : ∀ X0 : G, (σ X0) = (k (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq11824 X0
       have i₂ := eq1731 X0 (σ X0)
       grind)
    | exact superpose eq1731 eq11824
    | exact resolve eq11824 eq1731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731 eq11824
  have eq11870 : ∀ X0 : G, (σ X0) = (k (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11848 X0
       have i₂ := eq1525 X0
       grind)
    | exact superpose eq1525 eq11848
    | exact resolve eq11848 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11848
  have eq11885 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11870 X0
       have i₂ := eq1525 (M.op X0 X0)
       grind)
    | exact superpose eq1525 eq11870
    | exact resolve eq11870 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11870
  have eq11886 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11885 X0
       have i₂ := eq15 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq15 eq11885
    | exact resolve eq11885 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11885
  have eq11917 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq11886 X0
       grind)
    | exact superpose eq11886 eq10
    | exact resolve eq10 eq11886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11924 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq11886 X0
       grind)
    | exact superpose eq11886 eq23
    | exact resolve eq23 eq11886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11886
  have eq11988 : ∀ X0 X1 : G, (k (τ X1) X0) = (k (τ X1) (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq11924 X0 X1
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq11924
    | exact resolve eq11924 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11924
  have eq11995 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11917 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11917
    | exact resolve eq11917 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11917
  have eq12544 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) (k X1 (M.op (M.op X1 X1) (M.op X1 X1)))) ∨ (τ X0) = (M.op (τ X0) (k X1 (M.op (M.op X1 X1) (M.op X1 X1)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (k X1 (M.op (M.op X1 X1) (M.op X1 X1)))
       have i₂ := eq11988 X1 X0
       grind)
    | exact superpose eq11988 eq14
    | (have j0 := eq14 (τ X0) (k X1 (M.op (M.op X1 X1) (M.op X1 X1)))
       grind)
    | exact resolve eq14 eq11988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11988
  have eq12546 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (k X1 (M.op (M.op X1 X1) (M.op X1 X1)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12544 X0 X1
       have i₂ := eq11995 X1
       grind)
    | exact superpose eq11995 eq12544
    | (have j0 := eq12544 X0 X1
       grind)
    | exact resolve eq12544 eq11995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12544
  have eq12574 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (k X1 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq12546 X0 X1
       have j1 := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq12546 X0 X1
       have r₂ := eq12 (τ X0) X1
       grind)
    | exact resolve eq12546 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12546
  have eq12588 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12574 X0 X1
       have i₂ := eq11995 X1
       grind)
    | exact superpose eq11995 eq12574
    | (have j0 := eq12574 X0 X1
       grind)
    | exact resolve eq12574 eq11995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11995 eq12574
  have eq12654 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12588 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12588
    | exact resolve eq12588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12692 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 X0
       have i₂ := eq12588 X0 (τ X1)
       grind)
    | exact superpose eq12588 eq32
    | (have j1 := eq12588 X0 (τ X1)
       grind)
    | exact resolve eq32 eq12588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq12588
  have eq12955 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12654 (σ X0) (σ X1)
       grind)
    | exact superpose eq12654 eq15
    | (have j1 := eq12654 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq12654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17090 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq12692 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12692
  have eq17456 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17090 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq17090
    | (have j0 := eq17090 (σ X0) (σ X1)
       grind)
    | exact resolve eq17090 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17090
  have eq17512 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17456 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq17456
    | (have j0 := eq17456 X0 X1
       grind)
    | exact resolve eq17456 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17456
  have eq17528 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17512 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17512
    | (have j0 := eq17512 X0 X1
       grind)
    | exact resolve eq17512 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17512
  have eq17537 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17528 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq17528
    | (have j0 := eq17528 X0 X1
       grind)
    | exact resolve eq17528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17528
  have eq17544 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17537 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17537
    | (have j0 := eq17537 X0 X1
       grind)
    | exact resolve eq17537 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17537
  have eq18200 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17544 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq17544
    | (have j0 := eq17544 (σ X0) (σ X1)
       grind)
    | exact resolve eq17544 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20360 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12955 x y
       grind)
    | exact superpose eq12955 eq16
    | (have j1 := eq12955 x y
       grind)
    | exact resolve eq16 eq12955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12955
  have eq37853 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X0) (k X1 (σ X2))
       have i₂ := eq81 X0 X1 X2
       grind)
    | exact superpose eq81 eq13
    | (have j0 := eq13 (σ X0) (k X1 (σ X2))
       have j1 := eq81 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X0) (k X1 (σ X2))
       have r₂ := eq81 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq81 X0 X1 X2
       grind)
    | exact resolve eq13 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq37854 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37853 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37853
  have eq37855 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37854 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37854
  have eq37856 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X0 (k (τ X1) X2))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37855 X0 X1 X2
       have i₂ := eq21 X1 X2 X0
       grind)
    | exact superpose eq21 eq37855
    | (have j0 := eq37855 X0 X1 X2
       grind)
    | exact resolve eq37855 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq37855
  have eq37961 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (k (τ X1) X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37856 X0 X1 X2
       have i₂ := eq1525 X0
       grind)
    | exact superpose eq1525 eq37856
    | (have j0 := eq37856 X0 X1 X2
       grind)
    | exact resolve eq37856 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525 eq37856
  have eq47214 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (k X0 (τ (M.op (M.op X2 X2) (σ (M.op X0 X0))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1469 X0 X1
       have i₂ := eq6095 X0 X2
       grind)
    | exact superpose eq6095 eq1469
    | (have j0 := eq1469 X0 X1
       have j1 := eq6095 X0 X2
       grind)
    | (have r₁ := eq1469 X0 X1
       have r₂ := eq6095 X0 X1
       grind)
    | exact resolve eq1469 eq6095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469 eq6095
  have eq47362 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X2 X2) (σ (M.op X0 X0))))) = X0 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq47214 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47214
  have eq186894 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op (M.op X1 X1) (σ (M.op (τ X0) (τ X0))))))) ∨ (k (σ (τ X0)) X2) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (τ (M.op (M.op X1 X1) (σ (M.op (τ X0) (τ X0)))))
       have i₂ := eq47362 (τ X0) X2 X1
       grind)
    | exact superpose eq47362 eq17
    | (have j1 := eq47362 (τ X0) X2 X2
       grind)
    | exact resolve eq17 eq47362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47362
  have eq187090 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (M.op (M.op X1 X1) (σ (M.op (τ X0) (τ X0))))) ∨ (k (σ (τ X0)) X2) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186894 X0 X1 X2
       have i₂ := eq11 (M.op (M.op X1 X1) (σ (M.op (τ X0) (τ X0))))
       grind)
    | exact superpose eq11 eq186894
    | (have j0 := eq186894 X0 X1 X2
       grind)
    | exact resolve eq186894 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186894
  have eq187246 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (M.op (M.op X1 X1) (σ (τ (M.op X0 X0))))) ∨ (k (σ (τ X0)) X2) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187090 X0 X1 X2
       have i₂ := eq1519 X0
       grind)
    | exact superpose eq1519 eq187090
    | (have j0 := eq187090 X0 X1 X2
       grind)
    | exact resolve eq187090 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187090
  have eq187357 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) ∨ (k (σ (τ X0)) X2) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187246 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq187246
    | (have j0 := eq187246 X0 X1 X2
       grind)
    | exact resolve eq187246 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187246
  have eq187442 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 ∨ (k (σ (τ X0)) X2) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187357 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq187357
    | (have j0 := eq187357 X0 X1 X2
       grind)
    | exact resolve eq187357 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187357
  have eq187485 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187442 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq187442
    | (have j0 := eq187442 X0 X1 X2
       grind)
    | exact resolve eq187442 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187442
  have eq188448 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) ≠ X0 ∨ (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) = (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq187485 X0 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187485
  have eq188472 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) = (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq188448 X0 X1
       have j1 := eq12654 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq188448 X0 X1
       have r₂ := eq12654 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | exact resolve eq188448 eq12654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12654 eq188448
  have eq188579 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq188472 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq188472
    | exact resolve eq188472 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188472
  have eq188705 : ∀ X0 X1 : G, (k X1 (M.op (τ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq188579 X1 (τ X0)
       have i₂ := eq1519 X0
       grind)
    | exact superpose eq1519 eq188579
    | exact resolve eq188579 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188579
  have eq191095 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ (M.op X1 X1)) (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (τ (M.op X1 X1)) (M.op (τ X0) (τ X0)))
       have i₂ := eq188705 X1 (τ X0)
       grind)
    | exact superpose eq188705 eq17
    | exact resolve eq17 eq188705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188705
  have eq191254 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ (M.op X1 X1)) (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq191095 X0 X1
       have i₂ := eq1519 X0
       grind)
    | exact superpose eq1519 eq191095
    | exact resolve eq191095 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191095
  have eq191362 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ (M.op X1 X1)) (τ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq191254 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq191254
    | exact resolve eq191254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191254
  have eq203818 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (M.op X1 X1)) (τ (M.op (τ X0) (τ X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op (τ (M.op X1 X1)) (τ (M.op (τ X0) (τ X0)))))
       have i₂ := eq191362 (τ X0) X1
       grind)
    | exact superpose eq191362 eq17
    | exact resolve eq17 eq191362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191362
  have eq204011 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (M.op X0 X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq203818 X0 X1
       have i₂ := eq1519 X0
       grind)
    | exact superpose eq1519 eq203818
    | exact resolve eq203818 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203818
  have eq204203 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (M.op X0 X0))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq204011 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq204011
    | exact resolve eq204011 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204011
  have eq245852 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (M.op (τ X0) (τ X0))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (M.op (τ X0) (τ X0)))))))
       have i₂ := eq204203 (τ X0) X1
       grind)
    | exact superpose eq204203 eq17
    | exact resolve eq17 eq204203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204203
  have eq246052 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (τ (M.op X0 X0))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq245852 X0 X1
       have i₂ := eq1519 X0
       grind)
    | exact superpose eq1519 eq245852
    | exact resolve eq245852 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245852
  have eq246233 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (τ (M.op X0 X0))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq246052 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq246052
    | exact resolve eq246052 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246052
  have eq375684 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (τ (M.op (τ X0) (τ X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (τ (M.op (τ X0) (τ X0)))))))))
       have i₂ := eq246233 (τ X0) X1
       grind)
    | exact superpose eq246233 eq17
    | exact resolve eq17 eq246233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246233
  have eq376000 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (τ (τ (M.op X0 X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq375684 X0 X1
       have i₂ := eq1519 X0
       grind)
    | exact superpose eq1519 eq375684
    | exact resolve eq375684 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375684
  have eq376239 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (τ (τ (M.op X0 X0))))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq376000 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq376000
    | exact resolve eq376000 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376000
  have eq727264 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (τ (τ (M.op (τ X0) (τ X0))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (τ (τ (M.op (τ X0) (τ X0)))))))))))
       have i₂ := eq376239 (τ X0) X1
       grind)
    | exact superpose eq376239 eq17
    | exact resolve eq17 eq376239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376239
  have eq727810 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (τ (τ (τ (M.op X0 X0))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq727264 X0 X1
       have i₂ := eq1519 X0
       grind)
    | exact superpose eq1519 eq727264
    | exact resolve eq727264 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727264
  have eq728164 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (τ (τ (τ (M.op X0 X0))))))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq727810 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq727810
    | exact resolve eq727810 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727810
  have eq1851860 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (σ (τ (M.op X0 X0))) ∨ (σ (τ X0)) = (σ (k (τ X0) (k (τ X1) X2))) ∨ (σ (k (τ X0) (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37961 (τ X0) X1 X2
       have i₂ := eq1519 X0
       grind)
    | exact superpose eq1519 eq37961
    | (have j0 := eq37961 (τ X0) X1 X2
       grind)
    | exact resolve eq37961 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519 eq37961
  have eq1853352 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (σ (τ X0)) = (σ (k (τ X0) (k (τ X1) X2))) ∨ (σ (k (τ X0) (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1851860 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1851860
    | (have j0 := eq1851860 X0 X1 X2
       grind)
    | exact resolve eq1851860 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851860
  have eq1853401 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (τ X0)) = (σ (k (τ X0) (k (τ X1) X2))) ∨ (σ (k (τ X0) (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1853352 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1853352
    | (have j0 := eq1853352 X0 X1 X2
       grind)
    | exact resolve eq1853352 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853352
  have eq1853430 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (k (τ X1) X2))) ∨ (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1853401 X0 X1 X2
       have i₂ := eq17 X0 (k (τ X1) X2)
       grind)
    | exact superpose eq17 eq1853401
    | (have j0 := eq1853401 X0 X1 X2
       grind)
    | exact resolve eq1853401 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853401
  have eq1853459 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (k X1 (σ X2))) ∨ (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1853430 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq1853430
    | (have j0 := eq1853430 X0 X1 X2
       grind)
    | exact resolve eq1853430 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853430
  have eq1853488 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1853459 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1853459
    | (have j0 := eq1853459 X0 X1 X2
       grind)
    | exact resolve eq1853459 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853459
  have eq1853517 : ∀ X0 X1 X2 : G, (σ (k (τ X0) (k (τ X1) X2))) = (M.op X0 (k X1 (σ X2))) ∨ (k X0 (k X1 (σ X2))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1853488 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1853488
    | (have j0 := eq1853488 X0 X1 X2
       grind)
    | exact resolve eq1853488 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853488
  have eq1853542 : ∀ X0 X1 X2 : G, (k X0 (σ (k (τ X1) X2))) = (M.op X0 (k X1 (σ X2))) ∨ (k X0 (k X1 (σ X2))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1853517 X0 X1 X2
       have i₂ := eq17 X0 (k (τ X1) X2)
       grind)
    | exact superpose eq17 eq1853517
    | (have j0 := eq1853517 X0 X1 X2
       grind)
    | exact resolve eq1853517 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853517
  have eq1853560 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (k X0 (k X1 (σ X2))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1853542 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq1853542
    | (have j0 := eq1853542 X0 X1 X2
       grind)
    | exact resolve eq1853542 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1853542
  have eq1853573 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (k X0 (k X1 (σ X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1853560 X0 X1 X2
       have j1 := eq12 X0 (k X1 (σ X2))
       grind)
    | (have r₁ := eq1853560 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1853560 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853560
  have eq1853987 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1853573 X0 X0 (σ (σ (σ (σ (M.op (τ (M.op X1 X1)) (τ (τ (τ (τ (τ (M.op X0 X0)))))))))))
       have i₂ := eq728164 X0 X1
       grind)
    | exact superpose eq728164 eq1853573
    | exact resolve eq1853573 eq728164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728164 eq1853573
  have eq1858161 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq20360
       have i₂ := eq1853987 y x
       grind)
    | exact superpose eq1853987 eq20360
    | (have j1 := eq1853987 y x
       grind)
    | exact resolve eq20360 eq1853987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20360
  have eq1858163 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1853987 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853987
  have eq1858165 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq1858161
  have eq1864296 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1858163 (σ x) (σ y)
       have i₂ := eq1858165
       grind)
    | exact superpose eq1858165 eq1858163
    | (have j0 := eq1858163 (σ x) (σ y)
       grind)
    | (have r₁ := eq1858163 (σ x) (σ y)
       have r₂ := eq1858165
       grind)
    | exact resolve eq1858163 eq1858165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858165
  have eq1864297 : (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq1864296
  have eq1864299 : x = (k x y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq1864297
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1864297
    | exact resolve eq1864297 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864297
  have eq1864491 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq18200 x y
       have i₂ := eq1864299
       grind)
    | exact superpose eq1864299 eq18200
    | (have j0 := eq18200 x y
       grind)
    | (have r₁ := eq18200 x y
       have r₂ := eq1864299
       grind)
    | exact resolve eq18200 eq1864299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864299
  have eq1864571 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq1864491
  have eq1864583 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq18200 x y
       grind)
    | (have r₁ := eq1864571
       have r₂ := eq18200 x y
       grind)
    | exact resolve eq1864571 eq18200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18200 eq1864571
  have eq1868755 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1864583
       grind)
    | exact superpose eq1864583 eq16
    | exact resolve eq16 eq1864583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1868757 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1858163 (σ x) (σ y)
       have i₂ := eq1864583
       grind)
    | exact superpose eq1864583 eq1858163
    | (have j0 := eq1858163 (σ x) (σ y)
       grind)
    | (have r₁ := eq1858163 (σ x) (σ y)
       have r₂ := eq1864583
       grind)
    | exact resolve eq1858163 eq1864583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858163 eq1864583
  have eq1868758 : (σ x) = (k (σ x) (σ y)) := by grind
  clear eq1868757
  have eq1868760 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq1868758
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1868758
    | exact resolve eq1868758 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868758
  have eq1869307 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq1868760
       grind)
    | exact superpose eq1868760 eq10
    | exact resolve eq10 eq1868760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868760
  have eq1869909 : x = (k x y) := by
    first
    | (have i₁ := eq1869307
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1869307
    | exact resolve eq1869307 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869307
  have eq1869999 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17544 x y
       have i₂ := eq1869909
       grind)
    | exact superpose eq1869909 eq17544
    | (have j0 := eq17544 x y
       grind)
    | (have r₁ := eq17544 x y
       have r₂ := eq1869909
       grind)
    | exact resolve eq17544 eq1869909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17544 eq1869909
  have eq1870081 : x = (M.op x y) := by grind
  clear eq1869999
  have eq1875040 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1868755
       have i₂ := eq1870081
       grind)
    | exact superpose eq1870081 eq1868755
    | exact resolve eq1868755 eq1870081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868755 eq1870081
  have eq1875045 : False := by grind
  exact eq1875045
