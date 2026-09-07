import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation309`: `x ◇ x = x ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyx_y_pyx_Equation309 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law309 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law309.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X2) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X2 X1
       have j1 := eq14 X2 X1
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq42 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op (M.op X1 X1) X0) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq45 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq43 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq43 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq48 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq42 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq42 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq42 (M.op (k X1 X1) X0) X1
       have r₂ := eq12 X0 (k X1 X1)
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq49 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq38 X0 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | (have r₁ := eq38 (M.op X1 X0) X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X1 (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq50 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq49 X0 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | (have r₁ := eq49 (M.op X1 X0) X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X1 X1 (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq46
    | exact resolve eq46 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq46 (τ X1) X0
       grind)
    | exact superpose eq46 eq19
    | (have j1 := eq46 (τ X1) X0
       grind)
    | exact resolve eq19 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq69 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 X1)) ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq18 X0 X1
       grind)
    | (have i₁ := eq12 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 (M.op X1 X1) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq18 X0 X1
       grind)
    | (have i₁ := eq9 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X1 X1)) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X1 X1))) := by
    intro X0 X1
    grind
  clear eq18
  have eq132 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq128 X0 X1
       have j1 := eq69 (M.op (M.op X0 X1) (M.op X1 X1)) (M.op X0 X1)
       grind)
    | (have r₁ := eq128 X0 X1
       have r₂ := eq69 (M.op (M.op X0 X1) (M.op X1 X1)) (M.op X0 X1)
       grind)
    | exact resolve eq128 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq185 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq50
  have eq193 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq197 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq193 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq193
    | (have j0 := eq193 X0 X1
       grind)
    | exact resolve eq193 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq245 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X0
       have i₂ := eq14 X0 (σ X0)
       grind)
    | (have i₁ := eq40 X0 X1
       have i₂ := eq14 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq14 eq40
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq297 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq245 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq312 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq297 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq297 (M.op (σ (k X1 X1)) X0) X1
       have r₂ := eq12 X0 (σ (k X1 X1))
       grind)
    | (have r₁ := eq297 (M.op (σ X1) X0) X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq297 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq297 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq458 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68
    | exact resolve eq68 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq488 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq458 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq458
    | (have j0 := eq458 X0 X1
       grind)
    | exact resolve eq458 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq635 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63 y x
       grind)
    | exact superpose eq63 eq16
    | (have j1 := eq63 y x
       grind)
    | exact resolve eq16 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1051 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq1822 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq312
    | (have j0 := eq312 X1 (τ X0)
       grind)
    | exact resolve eq312 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq1936 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1822 X0 X1
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq1822
    | (have j0 := eq1822 X0 X1
       grind)
    | exact resolve eq1822 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1822
  have eq1950 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1936 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1936
    | (have j0 := eq1936 X0 X1
       grind)
    | exact resolve eq1936 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq1962 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1950 X0 X1
       have j1 := eq48 X1 X0
       grind)
    | (have r₁ := eq1950 X0 X1
       have r₂ := eq48 (k X0 X0) X1
       grind)
    | (have r₁ := eq1950 X0 X0
       have r₂ := eq48 X0 (k X0 X0)
       grind)
    | (have r₁ := eq1950 X0 X1
       have r₂ := eq48 (M.op X0 X1) (k X1 X0)
       grind)
    | exact resolve eq1950 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq1950
  have eq2000 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X0
       have i₂ := eq1962 X0 X1
       grind)
    | (have i₁ := eq46 X0 X1
       have i₂ := eq1962 X0 (k X0 X1)
       grind)
    | exact superpose eq1962 eq46
    | (have j0 := eq46 X0 X1
       have j1 := eq1962 X1 X0
       grind)
    | exact resolve eq46 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq2019 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (σ X1)
       have i₂ := eq1962 (σ X1) X0
       grind)
    | (have i₁ := eq32 X0 X1
       have i₂ := eq1962 X0 (k (σ X0) X1)
       grind)
    | exact superpose eq1962 eq32
    | (have j1 := eq1962 (σ X1) X0
       grind)
    | exact resolve eq32 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq2039 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X1 X1))) ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq132 X0 X1
       have i₂ := eq1962 (M.op X0 X1) (M.op (M.op X0 X1) (M.op X1 X1))
       grind)
    | exact superpose eq1962 eq132
    | (have j1 := eq1962 (M.op X0 X1) (M.op (M.op X0 X1) (M.op X1 X1))
       grind)
    | exact resolve eq132 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq2069 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 X1)) ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2039 X0 X1
       have i₂ := eq125 X0 X1
       grind)
    | exact superpose eq125 eq2039
    | (have j0 := eq2039 X0 X1
       grind)
    | exact resolve eq2039 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq2039
  have eq2082 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2019 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2019
    | (have j0 := eq2019 X0 X1
       grind)
    | exact resolve eq2019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq2094 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2000 X0 X1
       have j1 := eq1051 X1 X0
       grind)
    | (have r₁ := eq2000 X1 X1
       have r₂ := eq1051 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq2000 X0 X1
       have r₂ := eq1051 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq2000 X0 X1
       have r₂ := eq1051 X0 X1
       grind)
    | exact resolve eq2000 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051 eq2000
  have eq2105 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2069 X0 X1
       have j1 := eq124 X0 X1
       grind)
    | (have r₁ := eq2069 X0 X1
       have r₂ := eq124 X0 X1
       grind)
    | exact resolve eq2069 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq2069
  have eq14146 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2082 (σ X1) X0
       grind)
    | exact superpose eq2082 eq15
    | (have j1 := eq2082 (σ X1) X0
       grind)
    | exact resolve eq15 eq2082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082
  have eq14211 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14146 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq14146
    | (have j0 := eq14146 X0 X1
       grind)
    | exact resolve eq14146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14146
  have eq15958 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq635
       have i₂ := eq1962 x y
       grind)
    | exact superpose eq1962 eq635
    | (have j1 := eq1962 x y
       grind)
    | exact resolve eq635 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15961 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq635
       have i₂ := eq488 y x
       grind)
    | exact superpose eq488 eq635
    | (have j1 := eq488 y x
       grind)
    | (have r₁ := eq635
       have r₂ := eq488 y x
       grind)
    | exact resolve eq635 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq15966 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by grind
  clear eq15961
  have eq15969 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by grind
  clear eq15958
  have eq15977 : (M.op x y) = (τ (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq15966
       grind)
    | exact superpose eq15966 eq10
    | exact resolve eq10 eq15966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15966
  have eq16085 : x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq15977
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15977
    | exact resolve eq15977 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15977
  have eq16097 : x = (k y x) := by
    first
    | (have j1 := eq69 y x
       grind)
    | (have r₁ := eq16085
       have r₂ := eq69 y x
       grind)
    | exact resolve eq16085 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq16085
  have eq16376 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq47 y x
       have i₂ := eq16097
       grind)
    | exact superpose eq16097 eq47
    | (have j0 := eq47 y x
       grind)
    | exact resolve eq47 eq16097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq16385 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1962 x y
       have i₂ := eq16097
       grind)
    | exact superpose eq16097 eq1962
    | (have j0 := eq1962 x y
       grind)
    | exact resolve eq1962 eq16097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962
  have eq16764 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq17309 : (σ y) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq488 x x
       have i₂ := eq16385
       grind)
    | exact superpose eq16385 eq488
    | exact resolve eq488 eq16385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488 eq16385
  have eq17327 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17309
       have r₂ := eq16764
       grind)
    | exact resolve eq17309 eq16764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17309
  have eq32674 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2105 X1 X1
       have i₂ := eq2094 X0 X1
       grind)
    | (have i₁ := eq2105 X0 X1
       have i₂ := eq2094 (M.op X0 X1) X1
       grind)
    | exact superpose eq2094 eq2105
    | (have j1 := eq2094 (k X0 X0) X0
       grind)
    | exact resolve eq2105 eq2094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094 eq2105
  have eq33435 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq32674 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32674
  have eq33436 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq33435 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33435
  have eq34047 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33436 (σ X0)
       grind)
    | exact superpose eq33436 eq15
    | exact resolve eq15 eq33436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34110 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34047 X0
       have i₂ := eq33436 X0
       grind)
    | exact superpose eq33436 eq34047
    | exact resolve eq34047 eq33436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34047
  have eq36350 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq34110 X0
       grind)
    | exact superpose eq34110 eq9
    | exact resolve eq9 eq34110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38070 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36350 x
       have i₂ := eq17327
       grind)
    | exact superpose eq17327 eq36350
    | exact resolve eq36350 eq17327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17327 eq36350
  have eq39036 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38070
       grind)
    | exact superpose eq38070 eq16
    | exact resolve eq16 eq38070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38070
  have eq39845 : (σ y) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39036
       have i₂ := eq16376
       grind)
    | exact superpose eq16376 eq39036
    | exact resolve eq39036 eq16376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16376 eq39036
  have eq39853 : x = y ∨ x = (M.op x y) := by grind
  clear eq39845
  have eq39856 : x = (M.op x y) := by
    first
    | (have r₁ := eq39853
       have r₂ := eq16764
       grind)
    | exact resolve eq39853 eq16764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16764 eq39853
  have eq73812 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14211 x y
       grind)
    | exact superpose eq14211 eq16
    | (have j1 := eq14211 x y
       grind)
    | exact resolve eq16 eq14211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14211
  have eq73992 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq73812
       have i₂ := eq16097
       grind)
    | exact superpose eq16097 eq73812
    | exact resolve eq73812 eq16097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16097 eq73812
  have eq74313 : y = (k x x) := by
    first
    | (have r₁ := eq73992
       have r₂ := eq15969
       grind)
    | exact resolve eq73992 eq15969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15969 eq73992
  have eq74496 : y = (M.op x x) := by
    first
    | (have i₁ := eq74313
       have i₂ := eq33436 x
       grind)
    | exact superpose eq33436 eq74313
    | exact resolve eq74313 eq33436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33436 eq74313
  have eq77686 : y = (M.op x y) := by
    first
    | (have i₁ := eq9 x x
       have i₂ := eq74496
       grind)
    | exact superpose eq74496 eq9
    | exact resolve eq9 eq74496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74496
  have eq77715 : x = y := by
    first
    | (have i₁ := eq77686
       have i₂ := eq39856
       grind)
    | exact superpose eq39856 eq77686
    | exact resolve eq77686 eq39856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39856 eq77686
  have eq80796 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77715
       grind)
    | exact superpose eq77715 eq16
    | exact resolve eq16 eq77715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77715
  have eq80874 : False := by grind
  exact eq80874

/-- `Equation313`: `x ◇ x = y ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pyx_Equation313 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law313 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law313.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq10
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq63 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq64 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq68 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq28
  have eq90 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 X1 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq804 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq54
  have eq1419 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq90 X1 X0 x
       grind)
    | exact superpose eq90 eq9
    | exact resolve eq9 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq1805 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq10
    | (have j1 := eq64 X0 X1
       grind)
    | exact resolve eq10 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq95889 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq804 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq95891 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq95889 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95889
  have eq95892 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq95891 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95891
  have eq96109 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq95892 (σ X0)
       grind)
    | exact superpose eq95892 eq15
    | exact resolve eq15 eq95892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96115 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0 X0
       have i₂ := eq95892 (τ X0)
       grind)
    | exact superpose eq95892 eq68
    | exact resolve eq68 eq95892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq96122 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96115 X0
       have i₂ := eq95892 X0
       grind)
    | exact superpose eq95892 eq96115
    | exact resolve eq96115 eq95892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96115
  have eq96128 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96109 X0
       have i₂ := eq95892 X0
       grind)
    | exact superpose eq95892 eq96109
    | exact resolve eq96109 eq95892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95892 eq96109
  have eq97857 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq96122 X0
       grind)
    | exact superpose eq96122 eq9
    | exact resolve eq9 eq96122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96122
  have eq99444 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq96128 X0
       grind)
    | exact superpose eq96128 eq9
    | exact resolve eq9 eq96128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99447 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq99829 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq99447 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq99447
    | exact resolve eq99447 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99447
  have eq99881 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq99829
  have eq102906 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (M.op (τ X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1)
       have i₂ := eq97857 X1 X0
       grind)
    | exact superpose eq97857 eq11
    | exact resolve eq11 eq97857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97857
  have eq107011 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq102906 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq102906
    | exact resolve eq102906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107616 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X1) (σ (M.op X0 (M.op (τ (σ X1)) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq99444 X1 (σ X1)
       have i₂ := eq102906 X0 (σ X1)
       grind)
    | exact superpose eq102906 eq99444
    | exact resolve eq99444 eq102906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99444 eq102906
  have eq107703 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X1) (σ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq107616 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq107616
    | exact resolve eq107616 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107616
  have eq116725 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq118388 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116725 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq116725
    | (have j0 := eq116725 X0 X1
       grind)
    | exact resolve eq116725 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116725
  have eq119610 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op (σ X1) (M.op (σ X1) (σ (M.op X0 (M.op X1 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1419 (σ X0) (σ X0)
       have i₂ := eq107011 X0 X1
       grind)
    | exact superpose eq107011 eq1419
    | exact resolve eq1419 eq107011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419 eq107011
  have eq119766 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op (σ X1) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq119610 X0 X1
       have i₂ := eq107703 X0 X1
       grind)
    | exact superpose eq107703 eq119610
    | exact resolve eq119610 eq107703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107703 eq119610
  have eq245870 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq1805 X1 X0
       grind)
    | exact superpose eq1805 eq10
    | (have j1 := eq1805 X1 X0
       grind)
    | exact resolve eq10 eq1805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805
  have eq246340 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq245870 X0 X1
       have i₂ := eq96128 X0
       grind)
    | exact superpose eq96128 eq245870
    | (have j0 := eq245870 X0 X1
       grind)
    | exact resolve eq245870 eq96128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245870
  have eq246354 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq246340 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq246340
    | (have j0 := eq246340 X0 X1
       grind)
    | exact resolve eq246340 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246340
  have eq246363 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq246354 X0 X1
       have i₂ := eq96128 X1
       grind)
    | exact superpose eq96128 eq246354
    | (have j0 := eq246354 X0 X1
       grind)
    | exact resolve eq246354 eq96128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96128 eq246354
  have eq246366 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq246363 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq246363
    | (have j0 := eq246363 X0 X1
       grind)
    | exact resolve eq246363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246363
  have eq1271318 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq246366 y x
       grind)
    | exact superpose eq246366 eq16
    | (have j1 := eq246366 y x
       grind)
    | exact resolve eq16 eq246366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246366
  have eq1271322 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq118388 x y
       grind)
    | (have r₁ := eq1271318
       have r₂ := eq118388 x y
       grind)
    | exact resolve eq1271318 eq118388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118388 eq1271318
  have eq1271583 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99881 y
       have i₂ := eq1271322
       grind)
    | exact superpose eq1271322 eq99881
    | exact resolve eq99881 eq1271322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99881 eq1271322
  have eq1272179 : y = (M.op x x) := by
    first
    | (have r₁ := eq1271583
       have r₂ := eq16
       grind)
    | exact resolve eq1271583 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271583
  have eq1273522 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq119766 x x
       have i₂ := eq1272179
       grind)
    | exact superpose eq1272179 eq119766
    | exact resolve eq119766 eq1272179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119766 eq1272179
  have eq1273688 : False := by grind
  exact eq1273688

/-- `Equation325`: `x ◇ y = x ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_y_x_pxy_Equation325 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law325 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law325.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq29 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq10
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq58 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq68 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61
    | exact resolve eq61 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq78 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq164 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq46 X0 (τ X1)
       grind)
    | exact superpose eq46 eq21
    | (have j1 := eq46 X0 (τ X1)
       grind)
    | exact resolve eq21 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0
       have i₂ := eq46 X0 X1
       grind)
    | (have i₁ := eq26 X0
       have i₂ := eq46 X0 (M.op X0 X0)
       grind)
    | exact superpose eq46 eq26
    | (have j1 := eq46 X1 X0
       grind)
    | exact resolve eq26 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq173 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq194 : ∀ X0 : G, (τ (σ X0)) = (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq25 (τ (M.op (σ (σ X0)) (σ (σ X0)))) X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq25
    | exact resolve eq25 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 : G, (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq194 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq194
    | exact resolve eq194 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq211 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq47 X0 (τ X1)
       grind)
    | exact superpose eq47 eq21
    | (have j1 := eq47 X0 (τ X1)
       grind)
    | exact resolve eq21 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq47 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq47 X0 (M.op X1 X0)
       grind)
    | exact superpose eq47 eq9
    | (have j1 := eq47 X1 X0
       grind)
    | exact resolve eq9 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq261 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq50 (τ X1) X0
       grind)
    | exact superpose eq50 eq20
    | (have j1 := eq50 (τ X1) X0
       grind)
    | exact resolve eq20 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0
       have i₂ := eq50 X0 X1
       grind)
    | (have i₁ := eq26 X0
       have i₂ := eq50 X0 (M.op X0 X0)
       grind)
    | exact superpose eq50 eq26
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq26 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq50 (τ X1) X0
       grind)
    | exact superpose eq50 eq21
    | (have j1 := eq50 (τ X1) X0
       grind)
    | exact resolve eq21 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq309 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0
       have i₂ := eq46 X0 X1
       grind)
    | (have i₁ := eq86 X0
       have i₂ := eq46 X0 (M.op X0 X0)
       grind)
    | exact superpose eq46 eq86
    | (have j1 := eq46 X1 X0
       grind)
    | exact resolve eq86 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq86
  have eq537 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq57 X1 (σ X0)
       grind)
    | exact superpose eq57 eq34
    | (have j1 := eq57 X1 (σ X0)
       grind)
    | exact resolve eq34 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq57 X1 (τ X0)
       grind)
    | exact superpose eq57 eq20
    | (have j1 := eq57 X1 (τ X0)
       grind)
    | exact resolve eq20 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq546 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq57 X0 (τ X1)
       grind)
    | exact superpose eq57 eq21
    | (have j1 := eq57 X0 (τ X1)
       grind)
    | exact resolve eq21 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (τ X0) = (M.op X1 X1) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq540 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq540
    | (have j0 := eq540 X0 X1
       grind)
    | exact resolve eq540 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq567 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq537 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq537
    | (have j0 := eq537 X0 X1
       grind)
    | exact resolve eq537 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq666 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X0
       have i₂ := eq50 (σ X0) X1
       grind)
    | (have i₁ := eq54 X0 X1
       have i₂ := eq50 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq50 eq54
    | (have j1 := eq50 (σ X1) X0
       grind)
    | exact resolve eq54 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq669 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X0
       have i₂ := eq57 (σ X0) X1
       grind)
    | (have i₁ := eq54 X0 X1
       have i₂ := eq57 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq57 eq54
    | (have j1 := eq57 (σ X1) X0
       grind)
    | exact resolve eq54 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq731 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq10
    | (have j1 := eq54 X1 X0
       grind)
    | exact resolve eq10 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq54 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq803 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq802 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq825 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq669 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq828 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq666 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq2166 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq803 (τ X0)
       have i₂ := eq21 X0 (τ X0)
       grind)
    | exact superpose eq21 eq803
    | (have j0 := eq803 (τ X0)
       grind)
    | exact resolve eq803 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq2172 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2166 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2166
    | (have j0 := eq2166 X0
       grind)
    | exact resolve eq2166 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166
  have eq2177 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2172 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2172
    | (have j0 := eq2172 X0
       grind)
    | exact resolve eq2172 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172
  have eq2197 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2177 (τ X0)
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq2177
    | (have j0 := eq2177 (τ X0)
       grind)
    | exact resolve eq2177 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177
  have eq2767 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq182 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq3622 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq288 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3623 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq288 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq4439 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3622 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4574 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq4589 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4439 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq4439
    | exact resolve eq4439 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4439
  have eq7282 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op X0 X0) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2197 (σ X0)
       have i₂ := eq566 (σ X0) X0
       grind)
    | exact superpose eq566 eq2197
    | (have j0 := eq2197 (σ X0)
       have j1 := eq566 (σ X0) X0
       grind)
    | exact resolve eq2197 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq2197
  have eq7467 : ∀ X0 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op X0 X0) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq7282 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7282
  have eq7520 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (σ X0)) = (M.op X0 X0) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7467 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7467
    | (have j0 := eq7467 X0
       grind)
    | exact resolve eq7467 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7467
  have eq7578 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7520 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7520
    | (have j0 := eq7520 X0
       grind)
    | exact resolve eq7520 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7520
  have eq7579 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq7578 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7578
  have eq7613 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7579 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7579
    | (have j0 := eq7579 X0
       grind)
    | exact resolve eq7579 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7579
  have eq7676 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7613 (σ X0)
       grind)
    | exact superpose eq7613 eq15
    | (have j1 := eq7613 (σ X0)
       grind)
    | exact resolve eq15 eq7613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7613
  have eq8012 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq211 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq211
    | exact resolve eq211 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq8218 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8012 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq8012
    | (have j0 := eq8012 X0 X1
       grind)
    | exact resolve eq8012 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8012
  have eq10658 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq164 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq164
    | exact resolve eq164 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq10881 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10658 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq10658
    | (have j0 := eq10658 X0 X1
       grind)
    | exact resolve eq10658 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10658
  have eq11709 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1
       have i₂ := eq261 X0 X1
       grind)
    | (have i₁ := eq37 X0
       have i₂ := eq261 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq261 eq37
    | (have j1 := eq261 X0 X1
       grind)
    | exact resolve eq37 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq261
  have eq12206 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq280
    | exact resolve eq280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq12429 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12206 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq12206
    | (have j0 := eq12206 X0 X1
       grind)
    | exact resolve eq12206 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12206
  have eq12621 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq4589 X0
       grind)
    | exact superpose eq4589 eq68
    | (have j1 := eq4589 X0
       grind)
    | exact resolve eq68 eq4589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4589
  have eq12710 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12621 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq12621
    | (have j0 := eq12621 X0
       grind)
    | exact resolve eq12621 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12621
  have eq13394 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq21 X0 (k (τ X0) (τ X0))
       have i₂ := eq12710 (τ X0)
       grind)
    | exact superpose eq12710 eq21
    | (have j1 := eq12710 (τ X0)
       grind)
    | exact resolve eq21 eq12710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12710
  have eq13417 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13394 X0
       have i₂ := eq21 X0 (τ X0)
       grind)
    | exact superpose eq21 eq13394
    | (have j0 := eq13394 X0
       grind)
    | exact resolve eq13394 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13394
  have eq13436 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13417 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13417
    | (have j0 := eq13417 X0
       grind)
    | exact resolve eq13417 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13417
  have eq13452 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13436 X0
       have i₂ := eq21 X0 (τ X0)
       grind)
    | exact superpose eq21 eq13436
    | (have j0 := eq13436 X0
       grind)
    | exact resolve eq13436 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13436
  have eq13462 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13452 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13452
    | (have j0 := eq13452 X0
       grind)
    | exact resolve eq13452 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13452
  have eq14022 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 X0 (k (τ X0) (τ X0))
       have i₂ := eq13462 (τ X0)
       grind)
    | exact superpose eq13462 eq21
    | (have j1 := eq13462 (τ X0)
       grind)
    | exact resolve eq21 eq13462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14074 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq14022 X0
       have i₂ := eq21 X0 (τ X0)
       grind)
    | exact superpose eq21 eq14022
    | (have j0 := eq14022 X0
       grind)
    | exact resolve eq14022 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14022
  have eq14096 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq14074 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14074
    | (have j0 := eq14074 X0
       grind)
    | exact resolve eq14074 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14074
  have eq14110 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14096 X0
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq14096
    | (have j0 := eq14096 X0
       grind)
    | exact resolve eq14096 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14096
  have eq15483 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ (τ X0)) = (τ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq21 X0 (k (τ X0) (τ X0))
       have i₂ := eq14110 (τ X0)
       grind)
    | exact superpose eq14110 eq21
    | (have j1 := eq14110 (τ X0)
       grind)
    | exact resolve eq21 eq14110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14110
  have eq15506 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (τ (τ X0)) = (τ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15483 X0
       have i₂ := eq21 X0 (τ X0)
       grind)
    | exact superpose eq21 eq15483
    | (have j0 := eq15483 X0
       grind)
    | exact resolve eq15483 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15483
  have eq15528 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (τ (τ X0)) = (τ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15506 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15506
    | (have j0 := eq15506 X0
       grind)
    | exact resolve eq15506 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15506
  have eq15546 : ∀ X0 : G, (τ (τ X0)) = (τ (τ (k X0 X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15528 X0
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq15528
    | (have j0 := eq15528 X0
       grind)
    | exact resolve eq15528 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15528
  have eq15704 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq546
    | exact resolve eq546 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq15997 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15704 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq15704
    | (have j0 := eq15704 X0 X1
       grind)
    | exact resolve eq15704 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15704
  have eq20459 : ∀ X0 X1 : G, (k (τ (τ X0)) (τ X1)) = (τ (k (τ (k X0 X0)) X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1 (τ (k X0 X0))
       have i₂ := eq15546 X0
       grind)
    | exact superpose eq15546 eq58
    | (have j1 := eq15546 X0
       grind)
    | exact resolve eq58 eq15546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15546
  have eq20565 : ∀ X0 X1 : G, (τ (k (τ X0) X1)) = (τ (k (τ (k X0 X0)) X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20459 X0 X1
       have i₂ := eq58 X1 (τ X0)
       grind)
    | exact superpose eq58 eq20459
    | (have j0 := eq20459 X0 X1
       grind)
    | exact resolve eq20459 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20459
  have eq26553 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X1)
       have i₂ := eq825 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq825 (σ X0) X1
       grind)
    | exact superpose eq825 eq10
    | (have j1 := eq825 X0 X1
       grind)
    | exact resolve eq10 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq26720 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq26553 X0 X1
       have j1 := eq3622 X0 (σ X1)
       grind)
    | (have r₁ := eq26553 X0 X1
       have r₂ := eq3622 (τ X0) (k X1 X1)
       grind)
    | (have r₁ := eq26553 X0 X1
       have r₂ := eq3622 (k X1 X1) (τ X0)
       grind)
    | (have r₁ := eq26553 X0 X1
       have r₂ := eq3622 (k (σ X1) X0) (M.op (σ X1) X0)
       grind)
    | exact resolve eq26553 eq3622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3622 eq26553
  have eq28390 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq828
    | (have j0 := eq828 X1 (τ X0)
       grind)
    | exact resolve eq828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28635 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X1)
       have i₂ := eq828 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq828 (σ X0) X1
       grind)
    | exact superpose eq828 eq10
    | (have j1 := eq828 X0 X1
       grind)
    | exact resolve eq10 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq28799 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28635 X0 X1
       have j1 := eq3623 (σ X1) X0
       grind)
    | (have r₁ := eq28635 X0 X1
       have r₂ := eq3623 (τ X0) (k X1 X1)
       grind)
    | (have r₁ := eq28635 X0 X1
       have r₂ := eq3623 (k X1 X1) (τ X0)
       grind)
    | (have r₁ := eq28635 X0 X1
       have r₂ := eq3623 (k X0 (σ X1)) (M.op X0 (σ X1))
       grind)
    | exact resolve eq28635 eq3623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28635
  have eq28912 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28390 X0 X1
       have j1 := eq3623 X0 X1
       grind)
    | (have r₁ := eq28390 X0 X1
       have r₂ := eq3623 (k X0 X1) X1
       grind)
    | (have r₁ := eq28390 X0 X0
       have r₂ := eq3623 X0 (k X0 X0)
       grind)
    | (have r₁ := eq28390 X0 X1
       have r₂ := eq3623 (M.op X1 X0) (k X1 X0)
       grind)
    | exact resolve eq28390 eq3623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28390
  have eq29017 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28912 X0 X1
       have i₂ := eq21 X0 (τ X0)
       grind)
    | exact superpose eq21 eq28912
    | (have j0 := eq28912 X0 X1
       grind)
    | exact resolve eq28912 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28912
  have eq29053 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29017 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29017
    | (have j0 := eq29017 X0 X1
       grind)
    | exact resolve eq29017 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29017
  have eq35948 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq731 X1 X0
       grind)
    | exact superpose eq731 eq10
    | (have j1 := eq731 X1 X0
       grind)
    | exact resolve eq10 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq46303 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq7676 X0
       grind)
    | exact superpose eq7676 eq9
    | (have j1 := eq7676 X0
       grind)
    | exact resolve eq9 eq7676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7676
  have eq158680 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  clear eq8218
  have eq162576 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  clear eq10881
  have eq165912 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0
       have i₂ := eq12429 X0 X1
       grind)
    | (have i₁ := eq26 X0
       have i₂ := eq12429 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12429 eq26
    | (have j1 := eq12429 X1 X0
       grind)
    | exact resolve eq26 eq12429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq12429
  have eq165990 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq165912 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165912
  have eq741977 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (k X0 (τ (σ X1))) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1
       have i₂ := eq567 X0 (σ X1)
       grind)
    | exact superpose eq567 eq68
    | (have j1 := eq567 X0 (σ X1)
       grind)
    | exact resolve eq68 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq567
  have eq741989 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 (τ (σ X1))) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq741977 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq741977
    | (have j0 := eq741977 X0 X1
       grind)
    | exact resolve eq741977 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741977
  have eq742001 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq741989 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq741989
    | (have j0 := eq741989 X0 X1
       grind)
    | exact resolve eq741989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741989
  have eq742006 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq742001 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq742001
    | (have j0 := eq742001 X0 X1
       grind)
    | exact resolve eq742001 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742001
  have eq742163 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq742006 y x
       grind)
    | exact superpose eq742006 eq16
    | (have j1 := eq742006 y x
       grind)
    | exact resolve eq16 eq742006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742006
  have eq742179 : y = (k y x) ∨ x = (k y x) := by
    first
    | (have j1 := eq165990 x y
       grind)
    | (have r₁ := eq742163
       have r₂ := eq165990 x y
       grind)
    | exact resolve eq742163 eq165990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165990 eq742163
  have eq742260 : x ≠ y ∨ x = (k y x) := by grind
  clear eq742179
  have eq744110 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (τ (σ X0)) = (k X1 X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X1)
       have i₂ := eq26720 (σ X0) X1
       grind)
    | exact superpose eq26720 eq34
    | (have j1 := eq26720 (σ X0) X1
       grind)
    | exact resolve eq34 eq26720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq26720
  have eq744114 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (τ (σ X0)) = (k X1 X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq744110 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq744110
    | (have j0 := eq744110 X0 X1
       grind)
    | exact resolve eq744110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744110
  have eq744130 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (τ (σ X0)) = (k X1 X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq744114 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq744114
    | (have j0 := eq744114 X0 X1
       grind)
    | exact resolve eq744114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744114
  have eq744142 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 X1) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq744130 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq744130
    | (have j0 := eq744130 X0 X1
       grind)
    | exact resolve eq744130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744130
  have eq744146 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq744142 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq744142
    | (have j0 := eq744142 X0 X1
       grind)
    | exact resolve eq744142 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744142
  have eq744256 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (τ (σ X0)) = (k X1 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) X0
       have i₂ := eq28799 (σ X0) X1
       grind)
    | exact superpose eq28799 eq25
    | (have j1 := eq28799 (σ X0) X1
       grind)
    | exact resolve eq25 eq28799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28799
  have eq744260 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (τ (σ X0)) = (k X1 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq744256 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq744256
    | (have j0 := eq744256 X0 X1
       grind)
    | exact resolve eq744256 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744256
  have eq744276 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (σ X0)) = (k X1 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq744260 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq744260
    | (have j0 := eq744260 X0 X1
       grind)
    | exact resolve eq744260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744260
  have eq744288 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X1 X0) = X0 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq744276 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq744276
    | (have j0 := eq744276 X0 X1
       grind)
    | exact resolve eq744276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744276
  have eq744292 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X1) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq744288 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq744288
    | (have j0 := eq744288 X0 X1
       grind)
    | exact resolve eq744288 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744288
  have eq745213 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq744292 x y
       grind)
    | exact superpose eq744292 eq16
    | (have j1 := eq744292 x y
       grind)
    | exact resolve eq16 eq744292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745429 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq11709 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11709
  have eq745430 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq745429 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745429
  have eq745432 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq745430 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq745430
    | (have j0 := eq745430 X0
       grind)
    | exact resolve eq745430 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745430
  have eq745441 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq745432 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq745432
    | (have j0 := eq745432 X0
       grind)
    | exact resolve eq745432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745432
  have eq745476 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq46303 X0
       have i₂ := eq745441 X0
       grind)
    | exact superpose eq745441 eq46303
    | (have j0 := eq46303 X0
       have j1 := eq745441 X0
       grind)
    | exact resolve eq46303 eq745441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46303 eq745441
  have eq745537 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq745476 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745476
  have eq745685 : ∀ X0 : G, (k (τ (τ (σ (σ X0)))) X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq197 X0
       have i₂ := eq745537 (σ X0)
       grind)
    | exact superpose eq745537 eq197
    | (have j1 := eq745537 (σ X0)
       grind)
    | exact resolve eq197 eq745537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq745537
  have eq745734 : ∀ X0 : G, (k (τ (σ X0)) X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq745685 X0
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq745685
    | (have j0 := eq745685 X0
       grind)
    | exact resolve eq745685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745685
  have eq745744 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq745734 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq745734
    | (have j0 := eq745734 X0
       grind)
    | exact resolve eq745734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745734
  have eq745746 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq745744 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq745744
    | (have j0 := eq745744 X0
       grind)
    | exact resolve eq745744 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745744
  have eq745867 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq745746 X0
       grind)
    | exact superpose eq745746 eq9
    | (have j1 := eq745746 X0
       grind)
    | exact resolve eq9 eq745746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745746
  have eq746507 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq745867 X0
       have i₂ := eq29053 X0 X1
       grind)
    | (have i₁ := eq745867 X0
       have i₂ := eq29053 X0 (k X0 X0)
       grind)
    | exact superpose eq29053 eq745867
    | (have j1 := eq29053 X1 X0
       grind)
    | exact resolve eq745867 eq29053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29053 eq745867
  have eq746543 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq746507 X0 X1
       have j1 := eq3623 X1 X0
       grind)
    | (have r₁ := eq746507 X0 X1
       have r₂ := eq3623 (σ X0) (M.op (σ X1) (σ X0))
       grind)
    | (have r₁ := eq746507 X0 X1
       have r₂ := eq3623 (M.op (σ X1) (σ X0)) (σ X0)
       grind)
    | (have r₁ := eq746507 X0 X1
       have r₂ := eq3623 X0 X1
       grind)
    | exact resolve eq746507 eq3623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746507
  have eq751716 : ∀ X0 X1 : G, (k (τ (k X0 X0)) X1) = (σ (τ (k (τ X0) X1))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (τ (k X0 X0)) X1)
       have i₂ := eq20565 X0 X1
       grind)
    | exact superpose eq20565 eq11
    | (have j1 := eq20565 X0 X1
       grind)
    | exact resolve eq11 eq20565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20565
  have eq751728 : ∀ X0 X1 : G, (k (τ X0) X1) = (k (τ (k X0 X0)) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq751716 X0 X1
       have i₂ := eq11 (k (τ X0) X1)
       grind)
    | exact superpose eq11 eq751716
    | (have j0 := eq751716 X0 X1
       grind)
    | exact resolve eq751716 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751716
  have eq751781 : ∀ X0 X1 : G, (σ (k (τ X0) (τ X1))) = (k (σ (τ (k X0 X0))) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ (k X0 X0))
       have i₂ := eq751728 X0 (τ X1)
       grind)
    | exact superpose eq751728 eq21
    | (have j1 := eq751728 X0 X1
       grind)
    | exact resolve eq21 eq751728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751728
  have eq751805 : ∀ X0 X1 : G, (σ (k (τ X0) (τ X1))) = (k (k X0 X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq751781 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq751781
    | (have j0 := eq751781 X0 X1
       grind)
    | exact resolve eq751781 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751781
  have eq751826 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (k (k X0 X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq751805 X0 X1
       have i₂ := eq21 X1 (τ X0)
       grind)
    | exact superpose eq21 eq751805
    | (have j0 := eq751805 X0 X1
       grind)
    | exact resolve eq751805 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751805
  have eq751837 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq751826 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq751826
    | (have j0 := eq751826 X0 X1
       grind)
    | exact resolve eq751826 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751826
  have eq752086 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq751837 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751837
  have eq752110 : ∀ X0 : G, (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq752086 X0
       have j1 := eq13462 X0
       grind)
    | (have r₁ := eq752086 X0
       have r₂ := eq13462 X0
       grind)
    | exact resolve eq752086 eq13462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13462 eq752086
  have eq752179 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq752110 X1
       have i₂ := eq744292 X0 X1
       grind)
    | (have i₁ := eq752110 X0
       have i₂ := eq744292 (k X0 X0) X1
       grind)
    | exact superpose eq744292 eq752110
    | (have j1 := eq744292 X0 X1
       grind)
    | exact resolve eq752110 eq744292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744292
  have eq761978 : ∀ X0 : G, X0 ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq35948 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35948
  have eq761979 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq761978 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761978
  have eq761983 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq761979 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq761979
    | exact resolve eq761979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761979
  have eq762040 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq761983 X0
       have i₂ := eq21 X0 (τ X0)
       grind)
    | exact superpose eq21 eq761983
    | (have j0 := eq761983 X0
       grind)
    | exact resolve eq761983 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq761983
  have eq762043 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq762040 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq762040
    | (have j0 := eq762040 X0
       grind)
    | exact resolve eq762040 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762040
  have eq762131 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 (M.op X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (M.op X0 X0) X1
       have i₂ := eq762043 X0
       grind)
    | exact superpose eq762043 eq58
    | (have j1 := eq762043 X0
       grind)
    | exact resolve eq58 eq762043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762043
  have eq762153 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (k X1 (M.op X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq762131 X0 X1
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq762131
    | (have j0 := eq762131 X0 X1
       grind)
    | exact resolve eq762131 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq762131
  have eq762423 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (σ (τ (k X0 X1))) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 (M.op X1 X1))
       have i₂ := eq762153 X1 X0
       grind)
    | exact superpose eq762153 eq11
    | (have j1 := eq762153 X1 X1
       grind)
    | exact resolve eq11 eq762153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762153
  have eq762433 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq762423 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq762423
    | (have j0 := eq762423 X0 X1
       grind)
    | exact resolve eq762423 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762423
  have eq762517 : ∀ X0 : G, (M.op X0 X0) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq752110 (M.op X0 X0)
       have i₂ := eq762433 (M.op X0 X0) X0
       grind)
    | exact superpose eq762433 eq752110
    | (have j1 := eq762433 X0 X0
       grind)
    | exact resolve eq752110 eq762433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752110
  have eq762569 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq762517
  have eq762647 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq762433 X0 X0
       have i₂ := eq762569 X0
       grind)
    | exact superpose eq762569 eq762433
    | (have j0 := eq762433 X0 X0
       have j1 := eq762569 X0
       grind)
    | exact resolve eq762433 eq762569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762433 eq762569
  have eq762648 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq762647 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762647
  have eq762953 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq744146 X1 X0
       have i₂ := eq762648 X0
       grind)
    | exact superpose eq762648 eq744146
    | (have j0 := eq744146 X1 X0
       grind)
    | exact resolve eq744146 eq762648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744146
  have eq763109 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq762648 (σ X0)
       grind)
    | exact superpose eq762648 eq15
    | exact resolve eq15 eq762648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763215 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq763109 X0
       have i₂ := eq762648 X0
       grind)
    | exact superpose eq762648 eq763109
    | exact resolve eq763109 eq762648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763109
  have eq764799 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq763215 X0
       grind)
    | exact superpose eq763215 eq9
    | exact resolve eq9 eq763215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764801 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0) (σ X0)
       have i₂ := eq763215 X0
       grind)
    | exact superpose eq763215 eq19
    | exact resolve eq19 eq763215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764858 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq764801 X0
       have i₂ := eq763215 (M.op X0 X0)
       grind)
    | exact superpose eq763215 eq764801
    | exact resolve eq764801 eq763215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764801
  have eq765069 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq764858 X0
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq764858
    | exact resolve eq764858 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq764858
  have eq769931 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k x y) ∨ (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq746543 y x
       grind)
    | exact superpose eq746543 eq16
    | (have j1 := eq746543 y x
       grind)
    | exact resolve eq16 eq746543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746543
  have eq770435 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq752179 x y
       grind)
    | exact superpose eq752179 eq16
    | (have j1 := eq752179 x y
       grind)
    | exact resolve eq16 eq752179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752179
  have eq770461 : x = (k y x) ∨ y = (k x y) := by
    first
    | (have j1 := eq162576 y x
       grind)
    | (have r₁ := eq770435
       have r₂ := eq162576 y x
       grind)
    | exact resolve eq770435 eq162576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162576 eq770435
  have eq770538 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq225 x y
       have i₂ := eq770461
       grind)
    | exact superpose eq770461 eq225
    | (have j0 := eq225 x y
       grind)
    | exact resolve eq225 eq770461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770612 : y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq770538
  have eq770702 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq225 y x
       have i₂ := eq770612
       grind)
    | exact superpose eq770612 eq225
    | (have j0 := eq225 y x
       grind)
    | exact resolve eq225 eq770612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq770612
  have eq770705 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq770702
  have eq770729 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq770705
       grind)
    | exact superpose eq770705 eq9
    | exact resolve eq9 eq770705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770776 : x ≠ x ∨ x = (k y x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4574 y x
       have i₂ := eq770705
       grind)
    | exact superpose eq770705 eq4574
    | (have j0 := eq4574 y x
       grind)
    | (have r₁ := eq4574 y x
       have r₂ := eq770705
       grind)
    | (have r₁ := eq4574 x y
       have r₂ := eq770705
       grind)
    | exact resolve eq4574 eq770705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4574 eq770705
  have eq770805 : x = (k y x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq770776
  have eq770874 : y ≠ (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq770729
  have eq771614 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq762953 x y
       grind)
    | exact superpose eq762953 eq16
    | (have j1 := eq762953 x y
       grind)
    | exact resolve eq16 eq762953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762953
  have eq771653 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq15997 y x
       grind)
    | (have r₁ := eq771614
       have r₂ := eq15997 y x
       grind)
    | exact resolve eq771614 eq15997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15997 eq771614
  have eq771757 : x = y ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq770805
       have i₂ := eq771653
       grind)
    | exact superpose eq771653 eq770805
    | exact resolve eq770805 eq771653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770805
  have eq771863 : x = (M.op y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq771757
       have r₂ := eq770874
       grind)
    | exact resolve eq771757 eq770874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770874 eq771757
  have eq772336 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq765069 y
       have i₂ := eq771863
       grind)
    | exact superpose eq771863 eq765069
    | exact resolve eq765069 eq771863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765069 eq771863
  have eq772438 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq772336
       have r₂ := eq16
       grind)
    | exact resolve eq772336 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772336
  have eq772518 : (σ y) ≠ (σ y) ∨ y = (k x y) ∨ (k y x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq769931
       have i₂ := eq772438
       grind)
    | exact superpose eq772438 eq769931
    | exact resolve eq769931 eq772438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769931
  have eq772520 : (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq772438
       grind)
    | exact superpose eq772438 eq9
    | exact resolve eq9 eq772438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772531 : x = (k y x) ∨ (k y x) = (M.op y x) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq309 x y
       have i₂ := eq772438
       grind)
    | exact superpose eq772438 eq309
    | (have j0 := eq309 x y
       grind)
    | exact resolve eq309 eq772438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq772620 : x = (k y x) ∨ (k y x) = (M.op y x) ∨ x = y := by grind
  clear eq772531
  have eq772624 : y = (k x y) ∨ (k y x) = (M.op y x) ∨ x = y := by grind
  clear eq772518
  have eq772631 : (k y x) = (M.op y x) ∨ x = (k y x) := by
    first
    | (have r₁ := eq772620
       have r₂ := eq742260
       grind)
    | exact resolve eq772620 eq742260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742260 eq772620
  have eq772632 : (k y x) = (M.op y x) ∨ y = (k x y) := by
    first
    | (have j1 := eq3623 x y
       grind)
    | (have r₁ := eq772624
       have r₂ := eq3623 y (k x y)
       grind)
    | (have r₁ := eq772624
       have r₂ := eq3623 (k x y) y
       grind)
    | (have r₁ := eq772624
       have r₂ := eq3623 (k y x) (M.op y x)
       grind)
    | exact resolve eq772624 eq3623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3623 eq772624
  have eq772900 : y ≠ (M.op y x) ∨ y = (k y y) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq2767 y y
       have i₂ := eq772520
       grind)
    | exact superpose eq772520 eq2767
    | (have j0 := eq2767 y y
       grind)
    | exact resolve eq2767 eq772520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767 eq772520
  have eq772916 : y ≠ (M.op y x) ∨ y = (k y y) ∨ x = y := by grind
  clear eq772900
  have eq772926 : y ≠ (M.op y x) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq772916
       have i₂ := eq762648 y
       grind)
    | exact superpose eq762648 eq772916
    | exact resolve eq772916 eq762648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772916
  have eq773156 : y = (M.op y x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq772631
       have i₂ := eq771653
       grind)
    | exact superpose eq771653 eq772631
    | exact resolve eq772631 eq771653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773207 : x ≠ (M.op y x) ∨ x = (k y x) := by grind
  clear eq772631
  have eq773549 : x = (M.op y x) ∨ y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq770461
       have i₂ := eq772632
       grind)
    | exact superpose eq772632 eq770461
    | exact resolve eq770461 eq772632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770461 eq772632
  have eq773591 : y = (k x y) ∨ x = (M.op y x) := by grind
  clear eq773549
  have eq773622 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq745213
       have i₂ := eq773591
       grind)
    | exact superpose eq773591 eq745213
    | exact resolve eq745213 eq773591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745213
  have eq773647 : (σ (M.op x y)) = (σ y) ∨ x = (k y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq158680 y x
       have i₂ := eq773591
       grind)
    | exact superpose eq773591 eq158680
    | (have j0 := eq158680 y x
       grind)
    | exact resolve eq158680 eq773591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158680 eq773591
  have eq773677 : (σ (M.op x y)) = (σ y) ∨ x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq773647
  have eq773704 : (σ (M.op x y)) = (σ y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq773677
       have r₂ := eq773207
       grind)
    | exact resolve eq773677 eq773207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773677
  have eq773707 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq773622
       have r₂ := eq773207
       grind)
    | exact resolve eq773622 eq773207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773207 eq773622
  have eq773709 : x = (k y y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq773707
       have r₂ := eq773704
       grind)
    | exact resolve eq773707 eq773704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773704 eq773707
  have eq773711 : x = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq773709
       have i₂ := eq762648 y
       grind)
    | exact superpose eq762648 eq773709
    | exact resolve eq773709 eq762648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762648 eq773709
  have eq773762 : x = (M.op y y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq771653
       have i₂ := eq773711
       grind)
    | exact superpose eq773711 eq771653
    | exact resolve eq771653 eq773711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771653 eq773711
  have eq774299 : y ≠ y ∨ y = (M.op y y) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq772926
       have i₂ := eq773156
       grind)
    | exact superpose eq773156 eq772926
    | (have r₁ := eq772926
       have r₂ := eq773156
       grind)
    | exact resolve eq772926 eq773156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772926 eq773156
  have eq774333 : y ≠ y ∨ y = (M.op y y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq774299
  have eq774334 : y = (M.op y y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq774333
  have eq774737 : x = y ∨ x = y ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq774334
       have i₂ := eq773762
       grind)
    | exact superpose eq773762 eq774334
    | exact resolve eq774334 eq773762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773762 eq774334
  have eq774931 : y = (M.op x x) ∨ x = y := by grind
  clear eq774737
  have eq775259 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq764799 x
       have i₂ := eq774931
       grind)
    | exact superpose eq774931 eq764799
    | exact resolve eq764799 eq774931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764799 eq774931
  have eq776311 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq775259
       grind)
    | exact superpose eq775259 eq16
    | exact resolve eq16 eq775259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775259
  have eq776369 : (σ y) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq776311
       have i₂ := eq772438
       grind)
    | exact superpose eq772438 eq776311
    | exact resolve eq776311 eq772438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772438 eq776311
  have eq776373 : (σ y) ≠ (σ y) ∨ x = y := by grind
  clear eq776369
  have eq776374 : x = y := by grind
  clear eq776373
  have eq776377 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq776374
       grind)
    | exact superpose eq776374 eq16
    | exact resolve eq16 eq776374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776374
  have eq776572 : False := by grind
  exact eq776572

/-- `Equation326`: `x ◇ y = x ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxx_y_pxy_Equation326 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law326 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law326.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq10
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq34 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq32 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq49 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq50 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X0 X0) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq102 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq157 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1
       have i₂ := eq49 X1 X0
       grind)
    | (have i₁ := eq34 X0
       have i₂ := eq49 X0 (M.op X0 X0)
       grind)
    | exact superpose eq49 eq34
    | (have j1 := eq49 X1 X0
       grind)
    | exact resolve eq34 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq162 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq157 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq216 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1
       have i₂ := eq55 X1 X0
       grind)
    | (have i₁ := eq34 X0
       have i₂ := eq55 X0 (M.op X0 X0)
       grind)
    | exact superpose eq55 eq34
    | (have j1 := eq55 X1 X0
       grind)
    | exact resolve eq34 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq228 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq397 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq162 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq162
    | exact resolve eq162 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq162 (τ X0) X1
       grind)
    | exact superpose eq162 eq22
    | (have j1 := eq162 (τ X0) X1
       grind)
    | exact resolve eq22 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq162 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq500 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X3 X0) = (M.op X3 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq50 X2 X3 X0
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq50 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq50 eq9
    | (have j1 := eq50 X0 X1 X2
       grind)
    | exact resolve eq9 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X1)) = (M.op X2 (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq50 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq50 eq15
    | (have j1 := eq50 (σ X1) X2 (σ X0)
       grind)
    | exact resolve eq15 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq725 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq228 X1 (σ X0)
       grind)
    | exact superpose eq228 eq28
    | (have j1 := eq228 X1 (σ X0)
       grind)
    | exact resolve eq28 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq726 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ X1) X0) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq228 X1 (τ X0)
       grind)
    | exact superpose eq228 eq23
    | (have j1 := eq228 X1 (τ X0)
       grind)
    | exact resolve eq23 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq228 (τ X1) X0
       grind)
    | exact superpose eq228 eq23
    | (have j1 := eq228 (τ X1) X0
       grind)
    | exact resolve eq23 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq747 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq726 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq726
    | (have j0 := eq726 X0 X1
       grind)
    | exact resolve eq726 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq748 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq725 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq725
    | (have j0 := eq725 X0 X1
       grind)
    | exact resolve eq725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq1584 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X2
       have i₂ := eq59 X0 X2
       grind)
    | exact superpose eq59 eq15
    | (have j1 := eq59 X0 X2
       grind)
    | exact resolve eq15 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1669 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq59 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1670 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1669 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669
  have eq3326 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1670 (τ X0)
       have i₂ := eq23 X0 (τ X0)
       grind)
    | exact superpose eq23 eq1670
    | (have j0 := eq1670 (τ X0)
       grind)
    | exact resolve eq1670 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3330 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3326 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3326
    | (have j0 := eq3326 X0
       grind)
    | exact resolve eq3326 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326
  have eq3336 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3330 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3330
    | (have j0 := eq3330 X0
       grind)
    | exact resolve eq3330 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3330
  have eq3395 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3336 (τ X0)
       have i₂ := eq102 X0 X0
       grind)
    | exact superpose eq102 eq3336
    | (have j0 := eq3336 (τ X0)
       grind)
    | exact resolve eq3336 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336
  have eq5814 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq747 X0 X1
       grind)
    | exact superpose eq747 eq22
    | (have j1 := eq747 X0 X1
       grind)
    | exact resolve eq22 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq6165 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (k (σ (τ X0)) X1) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 X1
       have i₂ := eq748 (τ X0) X1
       grind)
    | exact superpose eq748 eq102
    | (have j1 := eq748 (τ X0) X1
       grind)
    | exact resolve eq102 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6187 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (τ (σ X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq748 X0 (σ X1)
       grind)
    | exact superpose eq748 eq15
    | (have j1 := eq748 X0 (σ X1)
       grind)
    | exact resolve eq15 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq6220 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6187 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq6187
    | (have j0 := eq6187 X0 X1
       grind)
    | exact resolve eq6187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6187
  have eq6229 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6165 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6165
    | (have j0 := eq6165 X0 X1
       grind)
    | exact resolve eq6165 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6165
  have eq7393 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3395 X0
       have i₂ := eq6229 X0 X0
       grind)
    | exact superpose eq6229 eq3395
    | (have j0 := eq3395 X0
       have j1 := eq6229 X0 X0
       grind)
    | (have r₁ := eq3395 x
       have r₂ := eq6229 x x
       grind)
    | exact resolve eq3395 eq6229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3395 eq6229
  have eq7397 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7393 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7393
  have eq8109 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq500 X1 X0 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq8110 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq8109 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8109
  have eq14600 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6220 x y
       grind)
    | exact superpose eq6220 eq16
    | (have j1 := eq6220 x y
       grind)
    | exact resolve eq16 eq6220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14602 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq6220 X0 X0
       grind)
    | exact superpose eq6220 eq9
    | (have j1 := eq6220 X0 X0
       grind)
    | exact resolve eq9 eq6220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6220
  have eq18834 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7397 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7397
    | (have j0 := eq7397 (σ X0)
       grind)
    | exact resolve eq7397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7397
  have eq18995 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18834 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq18834
    | (have j0 := eq18834 X0
       grind)
    | exact resolve eq18834 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18834
  have eq25782 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq409 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq409
    | exact resolve eq409 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq25984 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25782 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq25782
    | (have j0 := eq25782 X0 X1
       grind)
    | exact resolve eq25782 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25782
  have eq36961 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq734
    | exact resolve eq734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq37195 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36961 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq36961
    | (have j0 := eq36961 X0 X1
       grind)
    | exact resolve eq36961 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36961
  have eq38050 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq14600
       have i₂ := eq37195 y x
       grind)
    | exact superpose eq37195 eq14600
    | (have j1 := eq37195 y x
       grind)
    | (have r₁ := eq14600
       have r₂ := eq37195 y x
       grind)
    | exact resolve eq14600 eq37195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14600 eq37195
  have eq38110 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by grind
  clear eq38050
  have eq38111 : x = (k y x) := by grind
  clear eq38110
  have eq38256 : ∀ X0 : G, x = (M.op y x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq8110 X0 x y
       have i₂ := eq38111
       grind)
    | exact superpose eq38111 eq8110
    | (have j0 := eq8110 X0 y x
       grind)
    | exact resolve eq8110 eq38111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8110 eq38111
  have eq56621 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5814 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5814
    | (have j0 := eq5814 (σ X0) X1
       grind)
    | exact resolve eq5814 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5814
  have eq56925 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56621 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56621
    | (have j0 := eq56621 X0 X1
       grind)
    | exact resolve eq56621 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56621
  have eq56957 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56925 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq56925
    | (have j0 := eq56925 X0 X1
       grind)
    | exact resolve eq56925 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56925
  have eq61674 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq521 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq69815 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14602 X1 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq14602
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq14602 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14602
  have eq70300 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq69815 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69815
  have eq71944 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1670 X0
       have i₂ := eq56957 X0 X0
       grind)
    | exact superpose eq56957 eq1670
    | (have j0 := eq1670 X0
       have j1 := eq56957 X0 X0
       grind)
    | (have r₁ := eq1670 x
       have r₂ := eq56957 x x
       grind)
    | exact resolve eq1670 eq56957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56957
  have eq72056 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq71944 X0
       have j1 := eq1670 X0
       grind)
    | (have r₁ := eq71944 X0
       have r₂ := eq1670 X0
       grind)
    | exact resolve eq71944 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670 eq71944
  have eq179261 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq397 x y
       grind)
    | exact superpose eq397 eq16
    | (have j1 := eq397 x y
       grind)
    | exact resolve eq16 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq182480 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq179261
       have i₂ := eq25984 x y
       grind)
    | exact superpose eq25984 eq179261
    | (have j1 := eq25984 x y
       grind)
    | (have r₁ := eq179261
       have r₂ := eq25984 x y
       grind)
    | exact resolve eq179261 eq25984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182481 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by grind
  clear eq182480
  have eq185605 : (M.op x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq182481
       grind)
    | exact superpose eq182481 eq10
    | exact resolve eq10 eq182481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182481
  have eq185664 : y = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq185605
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq185605
    | exact resolve eq185605 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185605
  have eq185665 : y = (k x y) := by
    first
    | (have j1 := eq412 x y
       grind)
    | (have r₁ := eq185664
       have r₂ := eq412 x y
       grind)
    | exact resolve eq185664 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq185664
  have eq260825 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    grind
  clear eq1584
  have eq261736 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq260825 X0 X1
       have j1 := eq61674 X0 X1
       grind)
    | (have r₁ := eq260825 X0 X1
       have r₂ := eq61674 X0 X1
       grind)
    | (have r₁ := eq260825 X0 X0
       have r₂ := eq61674 X0 X0
       grind)
    | (have r₁ := eq260825 (k X0 X1) X0
       have r₂ := eq61674 X0 X1
       grind)
    | exact resolve eq260825 eq61674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61674 eq260825
  have eq458755 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = X0 ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq261736 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq261736
    | exact resolve eq261736 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458760 : ∀ X0 X1 : G, (M.op X0 X0) = (σ X1) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq261736 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq261736
    | exact resolve eq261736 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458875 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq458760 X0 X1
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq458760
    | (have j0 := eq458760 X0 X1
       grind)
    | exact resolve eq458760 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq458760
  have eq458876 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq458755 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq458755
    | (have j0 := eq458755 X0 X1
       grind)
    | exact resolve eq458755 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458755
  have eq468846 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq458875 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq458875
    | exact resolve eq458875 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468990 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq458875 X0 X1
       grind)
    | exact superpose eq458875 eq10
    | (have j1 := eq458875 X0 X1
       grind)
    | exact resolve eq10 eq458875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458875
  have eq473475 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq261736 X0 X0
       have i₂ := eq468846 X0 (σ X0)
       grind)
    | (have i₁ := eq261736 X0 X1
       have i₂ := eq468846 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq468846 eq261736
    | (have j1 := eq468846 X0 (σ X1)
       grind)
    | exact resolve eq261736 eq468846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261736
  have eq473613 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq468846 (τ X0) X1
       grind)
    | exact superpose eq468846 eq22
    | (have j1 := eq468846 (τ X0) X1
       grind)
    | exact resolve eq22 eq468846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473649 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq179261
       have i₂ := eq468846 x y
       grind)
    | exact superpose eq468846 eq179261
    | (have j1 := eq468846 x y
       grind)
    | exact resolve eq179261 eq468846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179261
  have eq473660 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq473649
  have eq491467 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq468990 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq468990
    | (have j0 := eq468990 X1 (τ X0)
       grind)
    | exact resolve eq468990 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468990
  have eq495270 : ∀ X0 X1 X2 : G, (k (τ X0) (τ X2)) = (τ (k (M.op X1 X1) X2)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102 X2 (M.op X1 X1)
       have i₂ := eq491467 X0 X1
       grind)
    | (have i₁ := eq102 X0 X0
       have i₂ := eq491467 X0 X1
       grind)
    | exact superpose eq491467 eq102
    | (have j1 := eq491467 X0 X1
       grind)
    | exact resolve eq102 eq491467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491467
  have eq495279 : ∀ X0 X1 X2 : G, (τ (k X0 X2)) = (τ (k (M.op X1 X1) X2)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq495270 X0 X1 X2
       have i₂ := eq102 X2 X0
       grind)
    | exact superpose eq102 eq495270
    | (have j0 := eq495270 X0 X1 X2
       grind)
    | exact resolve eq495270 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq495270
  have eq549263 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq473613 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq473613
    | exact resolve eq473613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549326 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1
       have i₂ := eq473613 X1 X0
       grind)
    | exact superpose eq473613 eq11
    | (have j1 := eq473613 X1 X0
       grind)
    | exact resolve eq11 eq473613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473613
  have eq549363 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq549263 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq549263
    | (have j0 := eq549263 X0 X1
       grind)
    | exact resolve eq549263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549263
  have eq671596 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq549326 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq549326
    | (have j0 := eq549326 X1 (σ X0)
       grind)
    | exact resolve eq549326 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549326
  have eq671668 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq671596 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq671596
    | (have j0 := eq671596 X0 X1
       grind)
    | exact resolve eq671596 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671596
  have eq1894639 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) X1) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k (M.op X2 X2) X1)
       have i₂ := eq495279 X0 X2 X1
       grind)
    | (have i₁ := eq11 (k X0 X2)
       have i₂ := eq495279 X0 X1 X2
       grind)
    | exact superpose eq495279 eq11
    | (have j1 := eq495279 X0 X2 X2
       grind)
    | exact resolve eq11 eq495279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495279
  have eq1894640 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1894639 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1894639
    | (have j0 := eq1894639 X0 X1 X2
       grind)
    | exact resolve eq1894639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894639
  have eq1894717 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k (M.op X1 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1894640 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894640
  have eq1894720 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1894717 X0 X1
       have i₂ := eq34 X1
       grind)
    | exact superpose eq34 eq1894717
    | (have j0 := eq1894717 X0 X1
       grind)
    | exact resolve eq1894717 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1894717
  have eq1894748 : ∀ X0 X1 : G, (σ X1) ≠ X0 ∨ (k (σ X1) (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1894720 (σ X1) (σ X1)
       have i₂ := eq458876 X0 X1
       grind)
    | (have i₁ := eq1894720 X0 X1
       have i₂ := eq458876 (M.op X0 X1) X1
       grind)
    | exact superpose eq458876 eq1894720
    | (have j0 := eq1894720 X0 (σ X1)
       have j1 := eq458876 X0 X1
       grind)
    | (have r₁ := eq1894720 (σ X1) (σ X1)
       have r₂ := eq458876 (σ X1) X1
       grind)
    | (have r₁ := eq1894720 X0 (M.op (σ X1) (σ X1))
       have r₂ := eq458876 (M.op X0 (M.op (σ X1) (σ X1))) X1
       grind)
    | exact resolve eq1894720 eq458876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458876 eq1894720
  have eq1894781 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) ≠ X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1894748 X0 X1
       have i₂ := eq15 X1 X1
       grind)
    | exact superpose eq15 eq1894748
    | (have j0 := eq1894748 X0 X1
       grind)
    | (have r₁ := eq1894748 (k (σ X0) (σ X1)) (k X0 X1)
       have r₂ := eq15 X0 X1
       grind)
    | exact resolve eq1894748 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894748
  have eq1894785 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1894781 X0 X1
       have j1 := eq473475 X0 X1
       grind)
    | (have r₁ := eq1894781 X0 (k X1 X1)
       have r₂ := eq473475 X0 X1
       grind)
    | (have r₁ := eq1894781 (σ (k X1 X1)) X1
       have r₂ := eq473475 (σ X1) X1
       grind)
    | (have r₁ := eq1894781 X0 X1
       have r₂ := eq473475 X0 X1
       grind)
    | exact resolve eq1894781 eq473475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473475 eq1894781
  have eq1894812 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X1)
       have i₂ := eq1894785 X0 (τ X1)
       grind)
    | (have i₁ := eq22 X0 X1
       have i₂ := eq1894785 (σ (k (τ X0) X1)) X1
       grind)
    | exact superpose eq1894785 eq22
    | (have j1 := eq1894785 X0 (τ X1)
       grind)
    | exact resolve eq22 eq1894785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1894813 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X1)
       have i₂ := eq1894785 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1894785 (σ X0) X1
       grind)
    | exact superpose eq1894785 eq10
    | (have j1 := eq1894785 X0 X1
       grind)
    | exact resolve eq10 eq1894785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894785
  have eq1894829 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1894812 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1894812
    | (have j0 := eq1894812 X0 X1
       grind)
    | exact resolve eq1894812 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894812
  have eq1894835 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1894829 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1894829
    | (have j0 := eq1894829 X0 X1
       grind)
    | exact resolve eq1894829 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894829
  have eq1895690 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1894813 (σ X0) X1
       grind)
    | exact superpose eq1894813 eq15
    | (have j1 := eq1894813 (σ X0) X1
       grind)
    | exact resolve eq15 eq1894813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894813
  have eq1895694 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1895690 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1895690
    | (have j0 := eq1895690 X0 X1
       grind)
    | exact resolve eq1895690 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895690
  have eq1896099 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1895694 x y
       grind)
    | exact superpose eq1895694 eq16
    | (have j1 := eq1895694 x y
       grind)
    | exact resolve eq16 eq1895694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1896110 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1896099
       have i₂ := eq185665
       grind)
    | exact superpose eq185665 eq1896099
    | exact resolve eq1896099 eq185665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185665 eq1896099
  have eq1896135 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1896110
       have i₂ := eq473660
       grind)
    | exact superpose eq473660 eq1896110
    | (have r₁ := eq1896110
       have r₂ := eq473660
       grind)
    | exact resolve eq1896110 eq473660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473660 eq1896110
  have eq1896144 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq1896135
  have eq1896321 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq468846 y y
       have i₂ := eq1896144
       grind)
    | exact superpose eq1896144 eq468846
    | (have j0 := eq468846 x y
       grind)
    | exact resolve eq468846 eq1896144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468846
  have eq1896359 : x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1894835 y y
       have i₂ := eq1896144
       grind)
    | exact superpose eq1896144 eq1894835
    | exact resolve eq1894835 eq1896144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894835 eq1896144
  have eq1896364 : x = (M.op y y) ∨ x = y := by grind
  clear eq1896359
  have eq1896385 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq1896321
  have eq1896490 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq70300 y x
       have i₂ := eq1896364
       grind)
    | exact superpose eq1896364 eq70300
    | exact resolve eq70300 eq1896364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70300
  have eq1896570 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1896490 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896490
  have eq1896987 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq1896385
  have eq1897010 : x = (M.op y y) := by
    first
    | (have r₁ := eq1896987
       have r₂ := eq1896364
       grind)
    | exact resolve eq1896987 eq1896364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896364 eq1896987
  have eq1897031 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq38256 y
       have i₂ := eq1897010
       grind)
    | exact superpose eq1897010 eq38256
    | exact resolve eq38256 eq1897010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38256
  have eq1897035 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq1897010
       grind)
    | exact superpose eq1897010 eq9
    | exact resolve eq9 eq1897010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1897112 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq72056 y
       have i₂ := eq1897010
       grind)
    | exact superpose eq1897010 eq72056
    | (have j0 := eq72056 y
       grind)
    | exact resolve eq72056 eq1897010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897010
  have eq1897207 : x = (M.op y x) := by grind
  clear eq1897031
  have eq1900154 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1896570 (σ x)
       grind)
    | exact superpose eq1896570 eq16
    | exact resolve eq16 eq1896570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896570
  have eq1900155 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq1900154
       have i₂ := eq1897035 x
       grind)
    | exact superpose eq1897035 eq1900154
    | exact resolve eq1900154 eq1897035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897035 eq1900154
  have eq1902591 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq1900155
       have i₂ := eq1895694 x x
       grind)
    | exact superpose eq1895694 eq1900155
    | (have j1 := eq1895694 x x
       grind)
    | exact resolve eq1900155 eq1895694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895694
  have eq1902594 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1900155
       have i₂ := eq18995 x
       grind)
    | exact superpose eq18995 eq1900155
    | (have j1 := eq18995 x
       grind)
    | exact resolve eq1900155 eq18995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18995
  have eq1902601 : x = (M.op x x) ∨ x = y := by
    first
    | (have j1 := eq549363 x x
       grind)
    | (have r₁ := eq1902594
       have r₂ := eq549363 x x
       grind)
    | exact resolve eq1902594 eq549363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549363 eq1902594
  have eq1902603 : x = (k x x) ∨ x = y := by
    first
    | (have j1 := eq25984 x x
       grind)
    | (have r₁ := eq1902591
       have r₂ := eq25984 x x
       grind)
    | exact resolve eq1902591 eq25984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25984 eq1902591
  have eq1902674 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq72056 x
       have i₂ := eq1902601
       grind)
    | exact superpose eq1902601 eq72056
    | (have j0 := eq72056 x
       grind)
    | exact resolve eq72056 eq1902601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72056 eq1902601
  have eq1902733 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq1902674
  have eq1903192 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq671668 x x
       have i₂ := eq1902603
       grind)
    | exact superpose eq1902603 eq671668
    | (have j0 := eq671668 x x
       grind)
    | exact resolve eq671668 eq1902603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671668 eq1902603
  have eq1903193 : (σ x) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq1903192
  have eq1904482 : (σ x) ≠ (σ (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1900155
       have i₂ := eq1902733
       grind)
    | exact superpose eq1902733 eq1900155
    | exact resolve eq1900155 eq1902733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900155 eq1902733
  have eq1904586 : (σ x) ≠ (σ (M.op x x)) ∨ x = y := by grind
  clear eq1904482
  have eq1904626 : x = y := by
    first
    | (have r₁ := eq1904586
       have r₂ := eq1903193
       grind)
    | exact resolve eq1904586 eq1903193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903193 eq1904586
  have eq1904632 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1904626
       grind)
    | exact superpose eq1904626 eq16
    | exact resolve eq16 eq1904626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1904789 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1897112
       have i₂ := eq1904626
       grind)
    | exact superpose eq1904626 eq1897112
    | exact resolve eq1897112 eq1904626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897112
  have eq1904801 : x = (M.op x x) := by
    first
    | (have i₁ := eq1897207
       have i₂ := eq1904626
       grind)
    | exact superpose eq1904626 eq1897207
    | exact resolve eq1897207 eq1904626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897207 eq1904626
  have eq1904813 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1904789
  have eq1904852 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1904632
       have i₂ := eq1904801
       grind)
    | exact superpose eq1904801 eq1904632
    | exact resolve eq1904632 eq1904801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904632 eq1904801
  have eq1904853 : False := by grind
  exact eq1904853

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq27 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq27 X1 X0
       grind)
    | exact superpose eq27 eq9
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq12
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq27 X0 X0
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (k X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq54
    | exact resolve eq54 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq52 (σ X0)
       grind)
    | exact superpose eq52 eq15
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq61
    | exact resolve eq61 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq75 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 X2)) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X2 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq27 X0 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq27
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq27 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq86 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X2 X2) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X0 X1 X2
       have i₂ := eq37 X2 X2
       grind)
    | exact superpose eq37 eq75
    | (have j0 := eq75 X0 X1 X2
       grind)
    | exact resolve eq75 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq75
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq149 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X1
       have i₂ := eq57 X0 (σ X1)
       grind)
    | exact superpose eq57 eq15
    | exact resolve eq15 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq156 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X1
       have i₂ := eq52 X1
       grind)
    | exact superpose eq52 eq149
    | exact resolve eq149 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq149
  have eq851 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq83
    | (have j0 := eq83 (σ (k X0 X1)) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq897 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq894 X0 X1
       have j1 := eq86 X0 X1 x
       grind)
    | (have r₁ := eq894 x x
       have r₂ := eq86 x x x
       grind)
    | (have r₁ := eq894 X0 X1
       have r₂ := eq86 X0 X1 X0
       grind)
    | (have r₁ := eq894 X0 X1
       have r₂ := eq86 (M.op X0 X0) (M.op X0 X1) x
       grind)
    | exact resolve eq894 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq894
  have eq908 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq851 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq851
    | (have j0 := eq851 X0 X1
       grind)
    | exact resolve eq851 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq851
  have eq2011 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq2022 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq2011 X0 X1
       have j1 := eq908 X0 X1
       grind)
    | (have r₁ := eq2011 X0 X1
       have r₂ := eq908 X0 X1
       grind)
    | (have r₁ := eq2011 X0 X1
       have r₂ := eq908 (k X0 X1) (M.op X0 X0)
       grind)
    | (have r₁ := eq2011 X0 X1
       have r₂ := eq908 (M.op X0 X0) (k X0 X1)
       grind)
    | exact resolve eq2011 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908 eq2011
  have eq3444 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq897 (τ X0) X1
       grind)
    | exact superpose eq897 eq18
    | (have j1 := eq897 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq897
  have eq30465 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2022 x y
       grind)
    | exact superpose eq2022 eq16
    | (have j1 := eq2022 x y
       grind)
    | exact resolve eq16 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022
  have eq411097 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3444 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3444
    | exact resolve eq3444 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3444
  have eq411573 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq411097 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq411097
    | (have j0 := eq411097 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq411097 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411097
  have eq434446 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq30465
       have i₂ := eq411573 x y
       grind)
    | exact superpose eq411573 eq30465
    | (have j1 := eq411573 (σ x) (σ y)
       grind)
    | (have r₁ := eq30465
       have r₂ := eq411573 x y
       grind)
    | (have r₁ := eq30465
       have r₂ := eq411573 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq30465
       have r₂ := eq411573 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq30465 eq411573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30465 eq411573
  have eq434447 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq434446
  have eq434457 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq434447
       grind)
    | exact superpose eq434447 eq10
    | exact resolve eq10 eq434447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434447
  have eq434534 : x = y ∨ x = y := by
    first
    | (have i₁ := eq434457
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq434457
    | exact resolve eq434457 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434457
  have eq434535 : x = y := by grind
  clear eq434534
  have eq438669 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq434535
       grind)
    | exact superpose eq434535 eq16
    | exact resolve eq16 eq434535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434535
  have eq438670 : False := by grind
  exact eq438670

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq27 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq27 X1 X0
       grind)
    | exact superpose eq27 eq9
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq12
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq27 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq52
    | exact resolve eq52 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq52
  have eq75 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
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
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq148 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X1
       have i₂ := eq53 X0 (σ X1)
       grind)
    | exact superpose eq53 eq15
    | exact resolve eq15 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq155 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X1
       have i₂ := eq50 X1
       grind)
    | exact superpose eq50 eq148
    | exact resolve eq148 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq148
  have eq164 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq79 (σ X0) (σ X1)
       grind)
    | exact superpose eq79 eq15
    | (have j1 := eq79 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq79 (τ X0) X1
       grind)
    | exact superpose eq79 eq18
    | (have j1 := eq79 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq79
  have eq5797 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq165 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq165
    | exact resolve eq165 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq5859 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5797 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5797
    | (have j0 := eq5797 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq5797 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5797
  have eq8300 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq164 x y
       grind)
    | exact superpose eq164 eq16
    | (have j1 := eq164 x y
       grind)
    | exact resolve eq16 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq194925 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8300
       have i₂ := eq5859 x y
       grind)
    | exact superpose eq5859 eq8300
    | (have j1 := eq5859 (σ x) (σ y)
       grind)
    | (have r₁ := eq8300
       have r₂ := eq5859 x y
       grind)
    | (have r₁ := eq8300
       have r₂ := eq5859 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8300
       have r₂ := eq5859 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8300 eq5859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5859 eq8300
  have eq194926 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq194925
  have eq194930 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq194926
       grind)
    | exact superpose eq194926 eq10
    | exact resolve eq10 eq194926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194926
  have eq194978 : x = y ∨ x = y := by
    first
    | (have i₁ := eq194930
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq194930
    | exact resolve eq194930 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194930
  have eq194979 : x = y := by grind
  clear eq194978
  have eq197812 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq194979
       grind)
    | exact superpose eq194979 eq16
    | exact resolve eq16 eq194979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194979
  have eq197813 : False := by grind
  exact eq197813

/-- `Equation3279`: `x ◇ x = y ◇ (y ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation3279 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3279 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3279.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq38 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq38 (σ X0)
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq41
    | exact resolve eq41 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq41
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq210 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq213 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq210 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq210 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq210 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq210 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq210 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq252 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq213 (σ X0) (σ X1)
       grind)
    | exact superpose eq213 eq15
    | (have j1 := eq213 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq213 (τ X0) X1
       grind)
    | exact superpose eq213 eq18
    | (have j1 := eq213 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq213
  have eq2307 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq254 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq254
    | exact resolve eq254 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq2378 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2307 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2307
    | (have j0 := eq2307 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq2307 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307
  have eq6394 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq252 x y
       grind)
    | exact superpose eq252 eq16
    | (have j1 := eq252 x y
       grind)
    | exact resolve eq16 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq6775 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6394
       have i₂ := eq2378 x y
       grind)
    | exact superpose eq2378 eq6394
    | (have j1 := eq2378 (σ x) (σ y)
       grind)
    | (have r₁ := eq6394
       have r₂ := eq2378 x y
       grind)
    | (have r₁ := eq6394
       have r₂ := eq2378 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6394
       have r₂ := eq2378 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6394 eq2378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2378 eq6394
  have eq6776 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6775
  have eq6852 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6776
       grind)
    | exact superpose eq6776 eq10
    | exact resolve eq10 eq6776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6776
  have eq6904 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6852
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6852
    | exact resolve eq6852 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6852
  have eq6905 : x = y := by grind
  clear eq6904
  have eq7186 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6905
       grind)
    | exact superpose eq6905 eq16
    | exact resolve eq16 eq6905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6905
  have eq7187 : False := by grind
  exact eq7187

/-- `Equation3279`: `x ◇ x = y ◇ (y ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_x_pyx_Equation3279 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3279 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3279.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq38 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq38 (σ X0)
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq41
    | exact resolve eq41 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq41
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq63 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq63 (σ X1) (σ X0)
       grind)
    | exact superpose eq63 eq15
    | (have j1 := eq63 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq63 (τ X1) X0
       grind)
    | exact superpose eq63 eq18
    | (have j1 := eq63 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq63
  have eq634 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq69
    | exact resolve eq69 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq657 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq634 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq634
    | (have j0 := eq634 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq634 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq1551 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
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
  clear eq68
  have eq2290 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1551
       have i₂ := eq657 y x
       grind)
    | exact superpose eq657 eq1551
    | (have j1 := eq657 (σ x) (σ y)
       grind)
    | (have r₁ := eq1551
       have r₂ := eq657 y x
       grind)
    | (have r₁ := eq1551
       have r₂ := eq657 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1551
       have r₂ := eq657 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1551 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657 eq1551
  have eq2291 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2290
  have eq2503 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2291
       grind)
    | exact superpose eq2291 eq10
    | exact resolve eq10 eq2291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2291
  have eq2544 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2503
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2503
    | exact resolve eq2503 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503
  have eq2545 : x = y := by grind
  clear eq2544
  have eq2695 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2545
       grind)
    | exact superpose eq2545 eq16
    | exact resolve eq16 eq2545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2545
  have eq2696 : False := by grind
  exact eq2696
