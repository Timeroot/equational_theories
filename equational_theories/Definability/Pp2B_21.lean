import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_x_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  clear eq18
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq70 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq73 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq67 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq67
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq73
    | exact resolve eq73 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq73 X0 X0 x
       grind)
    | exact superpose eq73 eq52
    | exact resolve eq52 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq187 X0 X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq187
    | exact resolve eq187 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq205 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0 X0 X0
       have i₂ := eq194 X0
       grind)
    | exact superpose eq194 eq73
    | exact resolve eq73 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq206 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X0 X0 X1
       have i₂ := eq194 X0
       grind)
    | exact superpose eq194 eq52
    | exact resolve eq52 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq194
  have eq241 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq205 X0
       grind)
    | exact superpose eq205 eq9
    | exact resolve eq9 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq205 X0
       grind)
    | exact superpose eq205 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq205 X0
       grind)
    | exact resolve eq12 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq244 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq246 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq241 X0 X1
       have i₂ := eq72 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq241 X0 X1
       have i₂ := eq72 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq72 eq241
    | exact resolve eq241 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq241
  have eq468 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq246 X0 X1
       grind)
    | exact superpose eq246 eq9
    | exact resolve eq9 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq468 X0 X1
       have i₂ := eq205 X0
       grind)
    | exact superpose eq205 eq468
    | exact resolve eq468 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq486 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq246 X1 X0
       have i₂ := eq475 X1 X0
       grind)
    | exact superpose eq475 eq246
    | exact resolve eq246 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq489 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X0
       have i₂ := eq475 X1 X0
       grind)
    | exact superpose eq475 eq9
    | exact resolve eq9 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq82 X0 X0
       grind)
    | exact superpose eq82 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq82 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq82 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq716 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq675 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq720 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq716 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq716 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq716 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq1011 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq720 (M.op X0 X0) X1
       have i₂ := eq245 X0 (M.op X0 X0)
       grind)
    | exact superpose eq245 eq720
    | (have j0 := eq720 (M.op X0 X0) X1
       grind)
    | exact resolve eq720 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq1033 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1011 X0 X1
       have i₂ := eq205 X0
       grind)
    | exact superpose eq205 eq1011
    | (have j0 := eq1011 X0 X1
       grind)
    | exact resolve eq1011 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1034 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1033 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1087 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq475 X0 X2
       have i₂ := eq1034 X1 X0
       grind)
    | exact superpose eq1034 eq475
    | exact resolve eq475 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1115 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 (M.op X1 X1)
       have i₂ := eq1034 X1 X0
       grind)
    | exact superpose eq1034 eq23
    | exact resolve eq23 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1034
  have eq1175 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1087 (σ X0) X1 X2
       have i₂ := eq15 X0 (M.op X1 X1)
       grind)
    | exact superpose eq15 eq1087
    | exact resolve eq1087 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1244 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq1175 X0 x X2
       have i₂ := eq245 x X0
       grind)
    | exact superpose eq245 eq1175
    | exact resolve eq1175 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1350 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq486 X0 (σ (M.op X0 X0))
       have i₂ := eq1244 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq1244 eq486
    | exact resolve eq486 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1786 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1115 X0 x
       have i₂ := eq245 x (τ X0)
       grind)
    | exact superpose eq245 eq1115
    | exact resolve eq1115 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq1115
  have eq2054 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1786 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1786
    | exact resolve eq1786 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq2599 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq2054 X0
       grind)
    | exact superpose eq2054 eq11
    | exact resolve eq11 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054
  have eq4569 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq667
       have i₂ := eq2599 x
       grind)
    | exact superpose eq2599 eq667
    | exact resolve eq667 eq2599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq4570 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4569
       have i₂ := eq2599 y
       grind)
    | exact superpose eq2599 eq4569
    | exact resolve eq4569 eq2599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2599 eq4569
  have eq5427 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4570
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq4570
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq4570 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4570
  have eq5428 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq5427
  have eq29377 : (M.op y y) = (τ (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq5428
       grind)
    | exact superpose eq5428 eq10
    | exact resolve eq10 eq5428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5428
  have eq29472 : y = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq29377
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq29377
    | exact resolve eq29377 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29377
  have eq29473 : (σ y) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq29472
  have eq33951 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 (M.op (M.op X0 X0) X1)) (M.op X0 X2)) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X1) X0 (M.op X0 X2)
       have i₂ := eq204 X0 X0 X1 X2
       grind)
    | exact superpose eq204 eq9
    | exact resolve eq9 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq34022 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33951 X0 X1 X2
       have i₂ := eq475 X0 X1
       grind)
    | exact superpose eq475 eq33951
    | exact resolve eq33951 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33951
  have eq34352 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34022 (M.op (M.op X0 X0) (M.op X0 X1)) X2 X0
       have i₂ := eq206 X0 X1
       grind)
    | exact superpose eq206 eq34022
    | exact resolve eq34022 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq34022
  have eq34569 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34352 X0 X1 X2
       have i₂ := eq475 X0 (M.op X0 X1)
       grind)
    | exact superpose eq475 eq34352
    | exact resolve eq34352 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq34352
  have eq783890 : (M.op x x) = (τ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq29473
       grind)
    | exact superpose eq29473 eq10
    | exact resolve eq10 eq29473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29473
  have eq784449 : y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq783890
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq783890
    | exact resolve eq783890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783890
  have eq784450 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq784449
  have eq785148 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq34569 y y X0
       have i₂ := eq784450
       grind)
    | exact superpose eq784450 eq34569
    | exact resolve eq34569 eq784450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34569 eq784450
  have eq785163 : ∀ X0 : G, y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq785148 X0
       have i₂ := eq489 X0 y
       grind)
    | exact superpose eq489 eq785148
    | exact resolve eq785148 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq785148
  have eq785470 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq205 x
       have i₂ := eq785163 X0
       grind)
    | exact superpose eq785163 eq205
    | (have j1 := eq785163 y
       grind)
    | exact resolve eq205 eq785163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq785163
  have eq794045 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq785470 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785470
  have eq794046 : y = (M.op y y) := by grind
  clear eq794045
  have eq794388 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq486 X0 y
       have i₂ := eq794046
       grind)
    | exact superpose eq794046 eq486
    | exact resolve eq486 eq794046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq794430 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1350 y x
       have i₂ := eq794046
       grind)
    | exact superpose eq794046 eq1350
    | exact resolve eq1350 eq794046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350 eq794046
  have eq827992 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq794430 (σ x)
       grind)
    | exact superpose eq794430 eq16
    | exact resolve eq16 eq794430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794430
  have eq828396 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq827992
       have i₂ := eq794388 x
       grind)
    | exact superpose eq794388 eq827992
    | exact resolve eq827992 eq794388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794388 eq827992
  have eq828397 : False := by grind
  exact eq828397

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxx_pxy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X2) X1 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq43 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq43 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq15
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq44 (τ X0)
       grind)
    | exact superpose eq44 eq18
    | exact resolve eq18 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48
    | exact resolve eq48 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq53 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq46
    | exact resolve eq46 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq51 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq51
    | exact resolve eq51 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq51
  have eq60 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq69 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq60
    | (have j0 := eq60 X0 X1
       grind)
    | exact resolve eq60 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq92 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq23 X0 X1 X2 X3
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq92 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq92
    | exact resolve eq92 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq340 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq69 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq69 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq13 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq366 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq340 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq381 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq366 X0 X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq366
    | (have j0 := eq366 X0 X1
       grind)
    | exact resolve eq366 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq382 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq381 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq395 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq382 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq382
    | (have j0 := eq382 X0 X1
       grind)
    | exact resolve eq382 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq396 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq395 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq825 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 X0 x X0
       have i₂ := eq104 X0 X0 x
       grind)
    | exact superpose eq104 eq23
    | exact resolve eq23 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq856 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq396 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq396
    | exact resolve eq396 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq396 x y
       grind)
    | exact superpose eq396 eq16
    | (have j1 := eq396 x x
       grind)
    | exact resolve eq16 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq956 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq856 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq856
    | (have j0 := eq856 X0 X1
       grind)
    | exact resolve eq856 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq856
  have eq966 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq956
    | (have j0 := eq956 X0 X1
       grind)
    | exact resolve eq956 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq956
  have eq979 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq104 X0 X0 X0
       have i₂ := eq825 X0
       grind)
    | exact superpose eq825 eq104
    | exact resolve eq104 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq1308 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 (M.op X0 X0) (M.op X0 X0) x
       have i₂ := eq979 X0
       grind)
    | exact superpose eq979 eq104
    | exact resolve eq104 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq1323 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1308 X0 X1
       have i₂ := eq24 X0 X0 X1
       grind)
    | exact superpose eq24 eq1308
    | exact resolve eq1308 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1308
  have eq22706 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq1323 X0 X1
       grind)
    | exact superpose eq1323 eq9
    | exact resolve eq9 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq22799 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22706 X0 X1
       have i₂ := eq979 X0
       grind)
    | exact superpose eq979 eq22706
    | exact resolve eq22706 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq22706
  have eq23398 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22799 (σ X0) X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq22799
    | exact resolve eq22799 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq57740 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq966 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq966
    | (have j0 := eq966 X1 X1
       grind)
    | exact resolve eq966 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq58608 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22799 X0 X1
       have i₂ := eq57740 X2 X0
       grind)
    | exact superpose eq57740 eq22799
    | (have j1 := eq57740 X2 X0
       grind)
    | exact resolve eq22799 eq57740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57740
  have eq66518 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq879
       have i₂ := eq58608 x X0 y
       grind)
    | exact superpose eq58608 eq879
    | (have j1 := eq58608 x X0 x
       grind)
    | exact resolve eq879 eq58608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879 eq58608
  have eq66521 : ∀ X0 : G, (σ x) = (σ (M.op x x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq66518 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66518
  have eq66557 : ∀ X0 : G, (M.op x x) = (τ (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq66521 X0
       grind)
    | exact superpose eq66521 eq10
    | (have j1 := eq66521 X0
       grind)
    | exact resolve eq10 eq66521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66521
  have eq66808 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq66557 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq66557
    | (have j0 := eq66557 x
       grind)
    | exact resolve eq66557 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66557
  have eq67535 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq66808 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66808
  have eq67536 : x = (M.op x x) := by grind
  clear eq67535
  have eq68569 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22799 x X0
       have i₂ := eq67536
       grind)
    | exact superpose eq67536 eq22799
    | exact resolve eq22799 eq67536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22799
  have eq68582 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23398 x X0
       have i₂ := eq67536
       grind)
    | exact superpose eq67536 eq23398
    | exact resolve eq23398 eq67536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23398 eq67536
  have eq71587 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68582 (σ y)
       grind)
    | exact superpose eq68582 eq16
    | exact resolve eq16 eq68582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68582
  have eq71977 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq71587
       have i₂ := eq68569 y
       grind)
    | exact superpose eq68569 eq71587
    | exact resolve eq71587 eq68569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68569 eq71587
  have eq71978 : False := by grind
  exact eq71978

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxx_y_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op y X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 X0
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq313 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq542 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op x (M.op (M.op x y) X0)) y) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq544 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op y X1)) := by
    intro X1
    first
    | exact superpose eq174 eq542
    | exact resolve eq542 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq542
  have eq866 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by
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
  have eq869 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq882 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq916 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq933 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq881
       grind)
    | exact superpose eq881 eq40
    | exact resolve eq40 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq933
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq933
    | exact resolve eq933 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq933
  have eq936 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq934
    | exact resolve eq934 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq944 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq936 eq882
    | exact resolve eq882 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq951 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq944
       have r₂ := eq27
       grind)
    | exact resolve eq944 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq959 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq951 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq951
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq951
       grind)
    | exact resolve eq13 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq960 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq959 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq976 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq951
       have i₂ := eq960 sF3
       grind)
    | exact superpose eq960 eq951
    | exact resolve eq951 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951 eq960
  have eq983 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq976
  have eq989 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq983 eq152
    | exact resolve eq152 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq994 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq989
    | exact resolve eq989 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq997 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq917 y
       grind)
    | (have r₁ := eq994
       have r₂ := eq917 y
       grind)
    | exact resolve eq994 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1004 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 y y X0
       have i₂ := eq997
       grind)
    | exact superpose eq997 eq16
    | exact resolve eq16 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1009 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1004 X0
       have i₂ := eq544 X0
       grind)
    | (have i₁ := eq1004 X0
       have i₂ := eq544 (M.op y X0)
       grind)
    | exact superpose eq544 eq1004
    | exact resolve eq1004 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1090 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq1009 X0
       grind)
    | exact superpose eq1009 eq16
    | exact resolve eq16 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1097 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq997 eq1090
    | exact resolve eq1090 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997 eq1090
  have eq1102 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1009 X0
       have i₂ := eq1097 X0
       grind)
    | exact superpose eq1097 eq1009
    | exact resolve eq1009 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009 eq1097
  have eq1113 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1102 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1128 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1113 x
       grind)
    | exact superpose eq1113 eq18
    | (have j1 := eq1113 x
       grind)
    | exact resolve eq18 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1141 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1128
  have eq1151 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1141 eq869
    | (have r₁ := eq869
       have r₂ := eq1141
       grind)
    | exact resolve eq869 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq1156 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1151
  have eq1288 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1156 eq90
    | exact resolve eq90 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1156
  have eq1295 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1288
    | exact resolve eq1288 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1454 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1295 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1295
       grind)
    | exact resolve eq13 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1461 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1454 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq1631 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1295
       have i₂ := eq1461 sF3
       grind)
    | exact superpose eq1461 eq1295
    | exact resolve eq1295 eq1461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295 eq1461
  have eq1645 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq1631
  have eq1675 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1645 eq152
    | exact resolve eq152 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq1645
  have eq1680 : y = (k y y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1675
    | exact resolve eq1675 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1675
  have eq1687 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq917 y
       have i₂ := eq1680
       grind)
    | exact superpose eq1680 eq917
    | (have j0 := eq917 y
       grind)
    | (have r₁ := eq917 y
       have r₂ := eq1680
       grind)
    | exact resolve eq917 eq1680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680
  have eq1688 : y = (M.op y y) ∨ y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq1687
  have eq1691 : y = (k x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1688
       have r₂ := eq866
       grind)
    | exact resolve eq1688 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866 eq1688
  have eq1696 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq881
       have i₂ := eq1691
       grind)
    | exact superpose eq1691 eq881
    | exact resolve eq881 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq1697 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq1691
       grind)
    | exact superpose eq1691 eq35
    | exact resolve eq35 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1691
  have eq1699 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq1696
  have eq1702 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1697
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1697
    | exact resolve eq1697 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697
  have eq1716 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 y y X0
       have i₂ := eq1699
       grind)
    | exact superpose eq1699 eq16
    | exact resolve eq16 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1734 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1716 X0
       have i₂ := eq544 X0
       grind)
    | (have i₁ := eq1716 X0
       have i₂ := eq544 (M.op y X0)
       grind)
    | exact superpose eq544 eq1716
    | exact resolve eq1716 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq1716
  have eq1739 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1702 eq882
    | exact resolve eq882 eq1702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882 eq1702
  have eq1743 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1739
  have eq1750 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1141 eq1743
    | exact resolve eq1743 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141 eq1743
  have eq1922 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq1734 X0
       grind)
    | exact superpose eq1734 eq16
    | exact resolve eq16 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1941 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1699 eq1922
    | exact resolve eq1922 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699 eq1922
  have eq1952 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1734 X0
       have i₂ := eq1941 X0
       grind)
    | exact superpose eq1941 eq1734
    | exact resolve eq1734 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734 eq1941
  have eq1977 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1952 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq2009 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1977 x
       grind)
    | exact superpose eq1977 eq18
    | (have j1 := eq1977 x
       grind)
    | exact resolve eq18 eq1977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1977
  have eq2028 : y = (M.op x y) := by grind
  clear eq2009
  have eq2047 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2028
       grind)
    | exact superpose eq2028 eq24
    | exact resolve eq24 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2049 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq2028
       grind)
    | exact superpose eq2028 eq40
    | exact resolve eq40 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2057 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2047 eq20
    | exact resolve eq20 eq2047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2076 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2047 eq313
    | exact resolve eq313 eq2047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq2047
  have eq3136 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1750 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1750
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq1750
       grind)
    | exact resolve eq13 eq1750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3153 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq3136 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3136
  have eq7464 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1750
       have i₂ := eq3153 sF3
       grind)
    | exact superpose eq3153 eq1750
    | exact resolve eq1750 eq3153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750 eq3153
  have eq7486 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq7464
  have eq7517 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7486 eq2076
    | exact resolve eq2076 eq7486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076 eq7486
  have eq7529 : y = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31 eq7517
    | exact resolve eq7517 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq7517
  have eq7536 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7529
       have i₂ := eq2028
       grind)
    | exact superpose eq2028 eq7529
    | exact resolve eq7529 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028 eq7529
  have eq7543 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq917 (M.op x y)
       grind)
    | (have r₁ := eq7536
       have r₂ := eq917 (M.op x y)
       grind)
    | exact resolve eq7536 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq7536
  have eq7564 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7543 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq7543
       grind)
    | exact resolve eq13 eq7543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7572 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7543 eq16
    | exact resolve eq16 eq7543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7588 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7564 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7564
  have eq7597 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq180 eq7572
    | exact resolve eq7572 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq7572
  have eq7679 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7543
       have i₂ := eq7588 sF0
       grind)
    | exact superpose eq7588 eq7543
    | exact resolve eq7543 eq7588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7710 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7679
  have eq7744 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7710 eq2049
    | exact resolve eq2049 eq7710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049 eq7710
  have eq7756 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq7744
    | exact resolve eq7744 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq7744
  have eq7762 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2057 eq7756
    | exact resolve eq7756 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7756
  have eq7778 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7762 eq915
    | (have j0 := eq915 (σ y) (σ y)
       grind)
    | (have r₁ := eq915 (σ y) (σ y)
       have r₂ := eq7762
       grind)
    | exact resolve eq915 eq7762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq7762
  have eq7779 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7778
  have eq7780 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7779
  have eq7829 : (σ y) = (k (σ y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7780 eq7588
    | exact resolve eq7588 eq7780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7780
  have eq7843 : (σ y) = (k (σ y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7829
  have eq7998 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 X1)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f7998_13 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
      intro X0 X1 X2 X3
      grind
    have f7998_14 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f7998_22 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
      intro X0 X1 X2
      grind
    have f7998_23 : X0 ≠ (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 X1)) X0) := by grind
    have f7998_24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f7998_25 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
      intro X0
      first
      | (have j0 := f7998_14 X0
         grind)
      | (have r₁ := f7998_14 X0
         have r₂ := f7998_24
         grind)
      | exact resolve f7998_14 f7998_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7998_42 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 := by
      intro X0
      first
      | (have i₁ := f7998_22 X0 (M.op x y) (M.op x y)
         have i₂ := f7998_25 X0
         grind)
      | exact superpose f7998_25 f7998_22
      | exact resolve f7998_22 f7998_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7998_56 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 X1)) X0) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f7998_13 X0 (M.op x y) (M.op x y) X1
         have i₂ := f7998_25 X0
         grind)
      | exact superpose f7998_25 f7998_13
      | exact resolve f7998_13 f7998_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7998_66 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f7998_56 X0 X1
         have i₂ := f7998_42 (M.op X0 X1)
         grind)
      | exact superpose f7998_42 f7998_56
      | exact resolve f7998_56 f7998_42
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7998_87 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f7998_22 X1 X0 X0
         have i₂ := f7998_66 X0 X1
         grind)
      | exact superpose f7998_66 f7998_22
      | exact resolve f7998_22 f7998_66
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7998_128 : X0 ≠ (M.op (M.op X0 X1) X0) := by
      first
      | (have i₁ := f7998_23
         have i₂ := f7998_87 (M.op x y) (M.op X0 X1)
         grind)
      | exact superpose f7998_87 f7998_23
      | exact resolve f7998_23 f7998_87
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7998_143 : False := by
      first
      | (have r₁ := f7998_128
         have r₂ := f7998_66 X0 X1
         grind)
      | exact resolve f7998_128 f7998_66
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f7998_143
  clear eq176
  have eq7999 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7597 eq16
    | exact resolve eq16 eq7597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7597
  have eq8026 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7543 eq7999
    | exact resolve eq7999 eq7543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7999
  have eq8027 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X1)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq7543 eq7998
    | exact resolve eq7998 eq7543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7543 eq7998
  have eq8031 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq8026 eq8027
    | exact resolve eq8027 eq8026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8026 eq8027
  have eq8341 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq8031 X0 X1
       grind)
    | exact superpose eq8031 eq16
    | exact resolve eq16 eq8031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8394 : ∀ X0 X1 : G, (M.op (k X0 (M.op x y)) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq7588 eq8341
    | exact resolve eq8341 eq7588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7588 eq8341
  have eq8505 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7843 eq8394
    | exact resolve eq8394 eq7843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7843 eq8394
  have eq8567 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq8505 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8505
  have eq8627 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f8627_14 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f8627_15 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f8627_24 : (σ y) ≠ (M.op X0 (σ y)) := by grind
    have f8627_26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f8627_27 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
      intro X0
      first
      | (have j0 := f8627_15 X0
         grind)
      | (have r₁ := f8627_15 X0
         have r₂ := f8627_26
         grind)
      | exact resolve f8627_15 f8627_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8627_28 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
      intro X0 X1
      first
      | (have j0 := f8627_14 X0 X1
         grind)
      | (have r₁ := f8627_14 X0 X1
         have r₂ := f8627_26
         grind)
      | exact resolve f8627_14 f8627_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8627_29 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
      intro X0
      first
      | (have i₁ := f8627_28 (σ y) X0
         have i₂ := f8627_27 X0
         grind)
      | exact superpose f8627_27 f8627_28
      | exact resolve f8627_28 f8627_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8627_33 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f8627_24
         have i₂ := f8627_29 X0
         grind)
      | exact superpose f8627_29 f8627_24
      | (have r₁ := f8627_24
         have r₂ := f8627_29 X0
         grind)
      | exact resolve f8627_24 f8627_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8627_34 : False := by grind
    exact f8627_34
  clear eq8031 eq8567
  have eq8639 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq8627 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8627
  have eq8729 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8639 eq26
    | (have j1 := eq8639 (σ x)
       grind)
    | exact resolve eq26 eq8639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8639
  have eq8743 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8729
  have eq8761 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq8743 eq27
    | exact resolve eq27 eq8743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq8743
  have eq8767 : False := by grind
  exact eq8767

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq74 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 (M.op (M.op X1 X0) X2)) = (k (M.op X1 (M.op (M.op X1 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X0) X2)) = (k (M.op X1 (M.op (M.op X1 X0) X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq74 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq91 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq91 y x
       grind)
    | exact superpose eq91 eq69
    | (have j1 := eq91 y x
       grind)
    | exact resolve eq69 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq209 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X2 X0) X3)) = (M.op (M.op (M.op X1 (M.op (M.op X1 (M.op X2 (M.op (M.op X2 X0) X3))) X4)) X0) (M.op X2 (M.op (M.op X2 X0) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X2 (M.op (M.op X2 X0) X3)) X1 X4 X0
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op x y) X1)) = (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op x (M.op (M.op x y) X1))) X2)) y) (M.op x (M.op (M.op x y) X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq518 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1))) X2)) (σ y)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq519 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
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
  have eq523 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq523 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq523
    | exact resolve eq523 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq530 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq512 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq512
    | exact resolve eq512 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq536 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq527 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq527
    | (have j0 := eq527 x y
       grind)
    | exact resolve eq527 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq117 eq91
    | (have j0 := eq91 (σ y) (σ x)
       grind)
    | exact resolve eq91 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq694
    | exact resolve eq694 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq698 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq695
       have r₂ := eq27
       grind)
    | exact resolve eq695 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq703 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq698 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq698
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq698
       grind)
    | exact resolve eq12 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq705 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq703
  have eq774 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq705 eq117
    | exact resolve eq117 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq777 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq774
  have eq785 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq777 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq777
       grind)
    | exact resolve eq13 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq786 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq785 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq826 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq786 eq117
    | exact resolve eq117 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq786
  have eq831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq826
  have eq837 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq831
    | exact resolve eq831 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq839 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq837
       have r₂ := eq27
       grind)
    | exact resolve eq837 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq861 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 (M.op (M.op X0 y) X1)) x) y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y X0 X1 x
       have i₂ := eq839
       grind)
    | exact superpose eq839 eq52
    | exact resolve eq52 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq927 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 x) X1)) x) = (k (M.op (M.op X0 (M.op (M.op X0 x) X1)) x) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq519 eq75
    | (have j0 := eq75 (M.op x y) X1 x
       grind)
    | exact resolve eq75 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq519
  have eq939 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq927 x x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq927
    | exact resolve eq927 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq3057 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq530 X0 X0 x
       grind)
    | exact superpose eq530 eq52
    | exact resolve eq52 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq4992 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq503 X0 X0 x X0 X2
       have i₂ := eq530 X0 X0 x
       grind)
    | exact superpose eq530 eq503
    | exact resolve eq503 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11109 : y = (M.op (M.op (M.op y y) x) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq861 y y
       have i₂ := eq3057 y
       grind)
    | exact superpose eq3057 eq861
    | exact resolve eq861 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11165 : ∀ X0 : G, y = (M.op (M.op (M.op (M.op y y) (M.op y X0)) x) y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq861 (M.op y y) X0
       have i₂ := eq3057 y
       grind)
    | exact superpose eq3057 eq861
    | exact resolve eq861 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq11178 : (M.op (M.op y y) x) = (M.op (M.op (M.op y y) y) (M.op (M.op y y) x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq530 (M.op y y) x y
       have i₂ := eq11109
       grind)
    | exact superpose eq11109 eq530
    | exact resolve eq530 eq11109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11109
  have eq11208 : (M.op (M.op y y) x) = (M.op y (M.op (M.op y y) x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11178
       have i₂ := eq3057 y
       grind)
    | exact superpose eq3057 eq11178
    | exact resolve eq11178 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11178
  have eq11793 : (M.op y y) = (M.op (M.op (M.op y y) x) (M.op y y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq530 y y x
       have i₂ := eq11208
       grind)
    | exact superpose eq11208 eq530
    | exact resolve eq530 eq11208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11208
  have eq12118 : x = (M.op (M.op (M.op y y) (M.op y y)) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq14 x (M.op y y) (M.op y y)
       have i₂ := eq11793
       grind)
    | exact superpose eq11793 eq14
    | exact resolve eq14 eq11793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11793
  have eq12155 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11165 y
       have i₂ := eq12118
       grind)
    | exact superpose eq12118 eq11165
    | exact resolve eq11165 eq12118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11165 eq12118
  have eq12191 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12155
  have eq12192 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12191
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12191
    | exact resolve eq12191 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12191
  have eq12196 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12192 eq29
    | exact resolve eq29 eq12192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12192
  have eq12249 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq12196
    | exact resolve eq12196 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12196
  have eq12250 : y = (M.op x y) := by grind
  clear eq12249
  have eq12255 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq12250 eq20
    | exact resolve eq20 eq12250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq12291 : y = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq12250 eq939
    | exact resolve eq939 eq12250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12344 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12255
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12255
    | exact resolve eq12255 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq12255
  have eq12347 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq12344 eq26
    | exact resolve eq26 eq12344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq12697 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq12291
       grind)
    | exact superpose eq12291 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq12291
       grind)
    | exact resolve eq13 eq12291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12714 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq12697 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12697
  have eq12745 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq939 eq4992
    | exact resolve eq4992 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq12910 : x = (M.op (M.op (M.op x x) (M.op x y)) x) := by
    first
    | exact superpose eq536 eq4992
    | (have j0 := eq4992 x y
       grind)
    | exact resolve eq4992 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq12945 : ∀ X0 : G, (M.op x (M.op (M.op x y) X0)) = (M.op (M.op (M.op (M.op x x) x) y) (M.op x (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq517 (M.op x x) x x
       have i₂ := eq4992 x (M.op sF0 x)
       grind)
    | exact superpose eq4992 eq517
    | exact resolve eq517 eq4992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq12946 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (σ y)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq518 (M.op sF2 sF2) x sF2
       have i₂ := eq4992 sF2 (M.op sF4 x)
       grind)
    | exact superpose eq4992 eq518
    | exact resolve eq518 eq4992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq4992
  have eq13012 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (σ (M.op x y))) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq12344 eq12946
    | exact resolve eq12946 eq12344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12946
  have eq13013 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op (M.op (M.op (M.op x x) x) y) (M.op x (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq12250 eq12945
    | exact resolve eq12945 eq12250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12945
  have eq13017 : x = (M.op (M.op (M.op x x) y) x) := by
    first
    | exact superpose eq12250 eq12910
    | exact resolve eq12910 eq12250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12910
  have eq13055 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq12250 eq12745
    | exact resolve eq12745 eq12250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12745
  have eq13061 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ (M.op x y))) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq13012 X0
       have i₂ := eq3057 sF2
       grind)
    | exact superpose eq3057 eq13012
    | exact resolve eq13012 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13012
  have eq13062 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op (M.op x y) (M.op x (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq13013 X0
       have i₂ := eq3057 x
       grind)
    | exact superpose eq3057 eq13013
    | exact resolve eq13013 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13013
  have eq13065 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq13055 X0
       have i₂ := eq527 y X0
       grind)
    | (have i₁ := eq13055 X0
       have i₂ := eq527 y (M.op y X0)
       grind)
    | exact superpose eq527 eq13055
    | exact resolve eq13055 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13055
  have eq13067 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq12347 eq13061
    | exact resolve eq13061 eq12347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13061
  have eq13068 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op (M.op x y) (M.op x (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq13062 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13062
    | (have j0 := eq13062 X0
       grind)
    | exact resolve eq13062 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq13062
  have eq13069 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq12250 eq13065
    | (have j0 := eq13065 X0
       grind)
    | exact resolve eq13065 eq12250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13065
  have eq13071 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op x (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq12250 eq13068
    | exact resolve eq13068 eq12250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12250 eq13068
  have eq13077 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op (M.op x x) x) (M.op y X0)) (M.op y X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq503 y (M.op x x) x X0 X1
       have i₂ := eq13017
       grind)
    | exact superpose eq13017 eq503
    | exact resolve eq503 eq13017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq13079 : ∀ X0 X1 : G, (M.op (M.op x x) x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op x x) x)) X1)) y) (M.op (M.op x x) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq515 y X1 (M.op x x) x x
       have i₂ := eq13017
       grind)
    | exact superpose eq13017 eq515
    | exact resolve eq515 eq13017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq13082 : (M.op (M.op x x) y) = (M.op (M.op (M.op x x) x) (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq530 (M.op x x) y x
       have i₂ := eq13017
       grind)
    | exact superpose eq13017 eq530
    | exact resolve eq530 eq13017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13017
  have eq13112 : (M.op (M.op x x) y) = (M.op x (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq13082
       have i₂ := eq3057 x
       grind)
    | exact superpose eq3057 eq13082
    | exact resolve eq13082 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13082
  have eq13115 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq13079 X0 X1
       have i₂ := eq3057 x
       grind)
    | exact superpose eq3057 eq13079
    | exact resolve eq13079 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13079
  have eq13117 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x (M.op y X0)) (M.op y X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq13077 X0 X1
       have i₂ := eq3057 x
       grind)
    | exact superpose eq3057 eq13077
    | exact resolve eq13077 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13077
  have eq13415 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq13069 X0
       grind)
    | exact superpose eq13069 eq14
    | exact resolve eq14 eq13069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13069
  have eq13871 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (k x y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq13415 X0
       have i₂ := eq12291
       grind)
    | exact superpose eq12291 eq13415
    | exact resolve eq13415 eq12291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12291 eq13415
  have eq13965 : ∀ X0 : G, x = (k x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13871 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13871
  have eq14933 : x ≠ (M.op y x) ∨ x = (k x y) := by grind
  clear eq12714
  have eq14935 : x = (k x y) := by
    first
    | (have r₁ := eq14933
       have r₂ := eq13965 x
       grind)
    | exact resolve eq14933 eq13965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13965 eq14933
  have eq14999 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq14935
       grind)
    | exact superpose eq14935 eq44
    | exact resolve eq44 eq14935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq14935
  have eq15013 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq12344 eq14999
    | exact resolve eq14999 eq12344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14999
  have eq15022 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq15013
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15013
    | exact resolve eq15013 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15013
  have eq15070 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq15022 eq91
    | (have j0 := eq91 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq91 eq15022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq15022
  have eq15072 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq12347 eq15070
    | exact resolve eq15070 eq12347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15070
  have eq15077 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq15072
       have r₂ := eq27
       grind)
    | exact resolve eq15072 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15072
  have eq16498 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) (M.op (σ y) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq13067 eq209
    | exact resolve eq209 eq13067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq13067
  have eq16546 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) (M.op (σ (M.op x y)) X1)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq12344 eq16498
    | exact resolve eq16498 eq12344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12344 eq16498
  have eq16555 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ (M.op x y)) X1)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq16546 X0 X1
       have i₂ := eq527 sF2 (M.op sF2 (M.op sF4 X0))
       grind)
    | (have i₁ := eq16546 X0 X1
       have i₂ := eq527 sF2 (M.op sF4 X0)
       grind)
    | exact superpose eq527 eq16546
    | exact resolve eq16546 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq16546
  have eq16782 : (M.op x x) = (M.op (M.op (M.op x x) y) (M.op x x)) := by
    first
    | (have i₁ := eq530 x x y
       have i₂ := eq13112
       grind)
    | exact superpose eq13112 eq530
    | exact resolve eq530 eq13112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13112
  have eq16952 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x x) (M.op x X0)) y) x) := by
    intro X0
    first
    | (have i₁ := eq13115 (M.op x x) X0
       have i₂ := eq3057 x
       grind)
    | exact superpose eq3057 eq13115
    | exact resolve eq13115 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3057 eq13115
  have eq17251 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ x)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq15077 eq16555
    | exact resolve eq16555 eq15077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15077 eq16555
  have eq17653 : y = (M.op (M.op (M.op x x) (M.op x x)) y) := by
    first
    | (have i₁ := eq14 y (M.op x x) (M.op x x)
       have i₂ := eq16782
       grind)
    | exact superpose eq16782 eq14
    | exact resolve eq14 eq16782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16782
  have eq17735 : x = (M.op y x) := by
    first
    | (have i₁ := eq16952 x
       have i₂ := eq17653
       grind)
    | exact superpose eq17653 eq16952
    | exact resolve eq16952 eq17653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16952 eq17653
  have eq17821 : ∀ X0 : G, y = (M.op (M.op (M.op x x) (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq13117 x X0
       have i₂ := eq17735
       grind)
    | exact superpose eq17735 eq13117
    | exact resolve eq13117 eq17735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13117
  have eq17826 : ∀ X0 : G, x = (M.op (M.op y (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq17735
       grind)
    | exact superpose eq17735 eq14
    | exact resolve eq14 eq17735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17735
  have eq18073 : ∀ X0 : G, x = (M.op (M.op x (M.op y X0)) x) := by
    intro X0
    first
    | (have i₁ := eq17826 (M.op y X0)
       have i₂ := eq13071 X0
       grind)
    | exact superpose eq13071 eq17826
    | exact resolve eq17826 eq13071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13071 eq17826
  have eq18149 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x x) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op y X0) x x
       have i₂ := eq18073 X0
       grind)
    | exact superpose eq18073 eq14
    | exact resolve eq14 eq18073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18073
  have eq18471 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq17821 X0
       have i₂ := eq18149 X0
       grind)
    | exact superpose eq18149 eq17821
    | exact resolve eq17821 eq18149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17821 eq18149
  have eq18535 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq18471 X0
       grind)
    | exact superpose eq18471 eq14
    | exact resolve eq14 eq18471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18471
  have eq18664 : ∀ X0 X1 : G, (M.op (M.op y y) X0) = (M.op (M.op (M.op (M.op y y) X0) X1) (M.op (M.op y y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq530 (M.op y y) X0 X1
       have i₂ := eq18535 (M.op (M.op (M.op y y) X0) X1)
       grind)
    | exact superpose eq18535 eq530
    | exact resolve eq530 eq18535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq18702 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18664 X0 X1
       have i₂ := eq18535 X0
       grind)
    | exact superpose eq18535 eq18664
    | exact resolve eq18664 eq18535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18535 eq18664
  have eq19037 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq17251 x
       have i₂ := eq18702 sF2 (M.op sF4 x)
       grind)
    | exact superpose eq18702 eq17251
    | exact resolve eq17251 eq18702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17251 eq18702
  have eq19083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12347 eq19037
    | exact resolve eq19037 eq12347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12347 eq19037
  have eq19119 : False := by grind
  exact eq19119

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq72 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
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
  have eq73 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq91
    | (have j0 := eq91 (σ X0) (σ X1)
       grind)
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq91 y x
       grind)
    | exact superpose eq91 eq69
    | (have j1 := eq91 y x
       grind)
    | exact resolve eq69 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq117 eq91
    | (have j0 := eq91 (σ y) (σ x)
       grind)
    | exact resolve eq91 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq120
    | exact resolve eq120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq121
       have r₂ := eq27
       grind)
    | exact resolve eq121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq126 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq27
    | exact resolve eq27 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq37
  have eq147 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq136 eq16
    | exact resolve eq16 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq350 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq73
    | (have r₁ := eq73
       have r₂ := eq126
       grind)
    | exact resolve eq73 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq126
  have eq351 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq350
  have eq354 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq351 eq117
    | exact resolve eq117 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq358 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq354
  have eq363 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq358
       have r₂ := eq128
       grind)
    | exact resolve eq358 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq358
  have eq367 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq363 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq363
       grind)
    | exact resolve eq13 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq368 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq367 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq424 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq368 eq117
    | exact resolve eq117 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq368
  have eq427 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq424
  have eq432 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq427
    | exact resolve eq427 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq434 : y = (M.op x y) := by
    first
    | (have r₁ := eq432
       have r₂ := eq27
       grind)
    | exact resolve eq432 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq436 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq434 eq20
    | exact resolve eq20 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq434 eq72
    | (have r₁ := eq72
       have r₂ := eq434
       grind)
    | exact resolve eq72 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq444 : x = (M.op x x) ∨ y = (k y x) := by grind
  clear eq440
  have eq450 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq436
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq436
    | exact resolve eq436 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq486 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq450 eq26
    | exact resolve eq26 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq551 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq95
    | (have j0 := eq95 (M.op x y) X0
       grind)
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq95
  have eq561 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq434 eq551
    | (have j0 := eq551 X0
       grind)
    | exact resolve eq551 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq743 : (σ (k y x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq561 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq561
    | (have j0 := eq561 x
       grind)
    | exact resolve eq561 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq561
  have eq756 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq486 eq743
    | exact resolve eq743 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq769 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq756
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq756
    | exact resolve eq756 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq756
  have eq778 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq450 eq769
    | exact resolve eq769 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq783 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq486 eq778
    | exact resolve eq778 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486 eq778
  have eq784 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq783
       have r₂ := eq27
       grind)
    | exact resolve eq783 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq787 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq784 eq147
    | exact resolve eq147 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq784
  have eq790 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq434 eq787
    | exact resolve eq787 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq804 : x = (M.op x x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq444
       have i₂ := eq790
       grind)
    | exact superpose eq790 eq444
    | exact resolve eq444 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq810 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq804
       grind)
    | exact superpose eq804 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq804
       grind)
    | exact resolve eq13 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq811 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq810 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq880 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq790
       have i₂ := eq811 y
       grind)
    | exact superpose eq811 eq790
    | exact resolve eq790 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq811
  have eq888 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq880
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq880
    | exact resolve eq880 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq880
  have eq892 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq434 eq888
    | exact resolve eq888 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434 eq888
  have eq893 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq892
  have eq905 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq893 eq15
    | exact resolve eq15 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq906 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq905
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq905
    | exact resolve eq905 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq905
  have eq907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq450 eq906
    | exact resolve eq906 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq906
  have eq908 : False := by grind
  exact eq908

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxx_x_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op y X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op x (M.op (M.op x y) X0)) y) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq544 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op y X1)) := by
    intro X1
    first
    | exact superpose eq174 eq542
    | exact resolve eq542 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq542
  have eq886 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq895 : (M.op x y) = (k x y) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
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
  have eq905 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq916 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq916 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq919 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq886 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq920 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq919 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq919 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq919 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq923 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq920 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq920
    | (have j0 := eq920 (σ X0) X1
       grind)
    | exact resolve eq920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq1789 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1811 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1815 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1811 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1811
    | exact resolve eq1811 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq1820 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1789 X0 x x X3 X4
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1789
    | exact resolve eq1789 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789
  have eq6182 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq895
       grind)
    | exact superpose eq895 eq40
    | exact resolve eq40 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq6183 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6182
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6182
    | exact resolve eq6182 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6182
  have eq6187 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq6183
    | exact resolve eq6183 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6183
  have eq15221 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0 X0 x X0
       have i₂ := eq1820 X0 X0 x
       grind)
    | exact superpose eq1820 eq176
    | exact resolve eq176 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq15261 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1820 X0 X0 X0
       have i₂ := eq15221 X0
       grind)
    | exact superpose eq15221 eq1820
    | exact resolve eq1820 eq15221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15221
  have eq15465 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq15261 X0
       grind)
    | exact superpose eq15261 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq15261 X0
       grind)
    | exact resolve eq13 eq15261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15475 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq15465 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15465
  have eq15496 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15475 X2 X0
       have i₂ := eq15475 X1 X0
       grind)
    | exact superpose eq15475 eq15475
    | exact resolve eq15475 eq15475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15519 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15261 X0
       have i₂ := eq15475 X1 (M.op X0 X0)
       grind)
    | exact superpose eq15475 eq15261
    | exact resolve eq15261 eq15475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15261
  have eq15746 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (σ (k (M.op X0 X0) (M.op X1 X1))) ∨ (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq923 (M.op X0 X0) X2
       have i₂ := eq15496 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq923 (M.op X0 X0) X2
       have i₂ := eq15496 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq15496 eq923
    | (have j0 := eq923 (M.op X0 X0) X2
       grind)
    | exact resolve eq923 eq15496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq15496
  have eq15830 : ∀ X0 X2 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq15746 X0 x X2
       have i₂ := eq15519 X0 x
       grind)
    | exact superpose eq15519 eq15746
    | (have j0 := eq15746 X0 x X2
       grind)
    | exact resolve eq15746 eq15519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15519 eq15746
  have eq15831 : ∀ X0 X2 : G, (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have j0 := eq15830 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15830
  have eq16003 : ∀ X0 : G, (k y (M.op X0 X0)) = (τ (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op X0 X0)
       have i₂ := eq15831 X0 sF3
       grind)
    | exact superpose eq15831 eq47
    | exact resolve eq47 eq15831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq15831
  have eq16021 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16003 x
       have i₂ := eq15475 x y
       grind)
    | exact superpose eq15475 eq16003
    | exact resolve eq16003 eq15475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16003
  have eq16089 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq16021 eq14
    | exact resolve eq14 eq16021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16021
  have eq16283 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16089
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq16089
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq16089 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16362 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq16283
  have eq16423 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16362
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq16362
    | exact resolve eq16362 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq16362
  have eq16460 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16423
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16423
    | exact resolve eq16423 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16423
  have eq17405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6187 eq905
    | exact resolve eq905 eq6187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq6187
  have eq17416 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq17405
       have r₂ := eq27
       grind)
    | exact resolve eq17405 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17405
  have eq17422 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq16460 eq17416
    | exact resolve eq17416 eq16460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17416
  have eq17466 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq17422 eq152
    | exact resolve eq152 eq17422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17422
  have eq17480 : y = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq17466
    | exact resolve eq17466 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17466
  have eq17486 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq917 y
       grind)
    | (have r₁ := eq17480
       have r₂ := eq917 y
       grind)
    | exact resolve eq17480 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17480
  have eq17503 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq17486 eq1815
    | exact resolve eq1815 eq17486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17486
  have eq17509 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq16460 eq17503
    | exact resolve eq17503 eq16460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16460 eq17503
  have eq17535 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq17509 eq152
    | exact resolve eq152 eq17509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq17509
  have eq17548 : y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq17535
    | exact resolve eq17535 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq17535
  have eq17553 : y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq917 y
       grind)
    | (have r₁ := eq17548
       have r₂ := eq917 y
       grind)
    | exact resolve eq17548 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq17548
  have eq17586 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1820 y y x
       have i₂ := eq17553
       grind)
    | exact superpose eq17553 eq1820
    | exact resolve eq1820 eq17553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17590 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq17586 X0
       have i₂ := eq544 X0
       grind)
    | (have i₁ := eq17586 X0
       have i₂ := eq544 (M.op y X0)
       grind)
    | exact superpose eq544 eq17586
    | exact resolve eq17586 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17586
  have eq17929 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq17590 X0
       grind)
    | exact superpose eq17590 eq16
    | exact resolve eq16 eq17590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17590
  have eq17956 : ∀ X0 : G, y = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq17553 eq17929
    | exact resolve eq17929 eq17553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17553 eq17929
  have eq17976 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1815 y x
       have i₂ := eq17956 X0
       grind)
    | exact superpose eq17956 eq1815
    | (have j1 := eq17956 y
       grind)
    | exact resolve eq1815 eq17956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815 eq17956
  have eq18097 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq17976 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17976
  have eq18098 : y = (M.op y y) := by grind
  clear eq18097
  have eq18123 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16089
       have i₂ := eq18098
       grind)
    | exact superpose eq18098 eq16089
    | exact resolve eq16089 eq18098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16089
  have eq18131 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq15475 y X0
       have i₂ := eq18098
       grind)
    | exact superpose eq18098 eq15475
    | exact resolve eq15475 eq18098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15475
  have eq18154 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq1820 y y x
       have i₂ := eq18098
       grind)
    | exact superpose eq18098 eq1820
    | exact resolve eq1820 eq18098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq18158 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq18154 X0
       have i₂ := eq544 X0
       grind)
    | (have i₁ := eq18154 X0
       have i₂ := eq544 (M.op y X0)
       grind)
    | exact superpose eq544 eq18154
    | exact resolve eq18154 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq18154
  have eq18175 : (σ y) = (k (σ y) y) := by
    first
    | (have i₁ := eq18123
       have i₂ := eq18131 sF3
       grind)
    | exact superpose eq18131 eq18123
    | exact resolve eq18123 eq18131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18123
  have eq18182 : (σ y) = (k (σ y) y) := by
    first
    | (have i₁ := eq18175
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18175
    | exact resolve eq18175 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18175
  have eq18480 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq18158 X0
       grind)
    | exact superpose eq18158 eq16
    | exact resolve eq16 eq18158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18509 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18480 X0
       have i₂ := eq18098
       grind)
    | exact superpose eq18098 eq18480
    | exact resolve eq18480 eq18098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18098 eq18480
  have eq18522 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq18158 X0
       have i₂ := eq18509 X0
       grind)
    | exact superpose eq18509 eq18158
    | exact resolve eq18158 eq18509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18158
  have eq18566 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 y X1
       have i₂ := eq18509 (M.op (M.op y X0) X1)
       grind)
    | exact superpose eq18509 eq16
    | exact resolve eq16 eq18509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18580 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18566 X0 X1
       have i₂ := eq18509 X0
       grind)
    | exact superpose eq18509 eq18566
    | exact resolve eq18566 eq18509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18509 eq18566
  have eq19223 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq18522 x
       grind)
    | exact superpose eq18522 eq18
    | (have j1 := eq18522 x
       grind)
    | exact resolve eq18 eq18522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18522
  have eq19311 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq19223
       grind)
    | exact superpose eq19223 eq24
    | exact resolve eq24 eq19223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq19348 : (σ y) = (k (σ y) (M.op x y)) := by
    first
    | (have i₁ := eq18182
       have i₂ := eq19223
       grind)
    | exact superpose eq19223 eq18182
    | exact resolve eq18182 eq19223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18182
  have eq19373 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19311 eq20
    | exact resolve eq20 eq19311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq19311
  have eq21785 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq18580 X0 X1
       grind)
    | exact superpose eq18580 eq16
    | exact resolve eq16 eq18580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21830 : ∀ X0 X1 : G, (M.op (k X0 y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21785 X0 X1
       have i₂ := eq18131 X0
       grind)
    | exact superpose eq18131 eq21785
    | exact resolve eq21785 eq18131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18131 eq21785
  have eq21848 : ∀ X0 X1 : G, (M.op (k X0 (M.op x y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21830 X0 X1
       have i₂ := eq19223
       grind)
    | exact superpose eq19223 eq21830
    | exact resolve eq21830 eq19223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19223 eq21830
  have eq22089 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq19348 eq21848
    | exact resolve eq21848 eq19348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19348 eq21848
  have eq22310 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq22089 eq18580
    | exact resolve eq18580 eq22089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18580 eq22089
  have eq22468 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22310 eq26
    | (have j1 := eq22310 (σ x)
       grind)
    | exact resolve eq26 eq22310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq22310
  have eq22550 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq22468 eq27
    | exact resolve eq27 eq22468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq22468
  have eq22569 : False := by grind
  exact eq22569

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxx_pyy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq36
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
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
  have eq133 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq50
    | (have j0 := eq50 (M.op x y)
       grind)
    | exact resolve eq50 eq20
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq344 : ∀ X0 : G, (k (σ X0) (k (σ (M.op x y)) (σ (M.op x y)))) = (σ (k X0 (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq133 eq38
    | exact resolve eq38 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq370 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq397 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq313 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq313
    | exact resolve eq313 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq527 : ∀ X0 : G, (τ (k X0 (k (σ y) (σ y)))) = (k (τ X0) (k y y)) := by
    intro X0
    first
    | exact superpose eq115 eq397
    | exact resolve eq397 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq11 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq893 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq904 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq904 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq907 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq874 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq908 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq907 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq907 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq907 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq910 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq908 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq908
    | (have j0 := eq908 (σ X0) X1
       grind)
    | exact resolve eq908 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq1835 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq910 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq910
    | (have j0 := eq910 X0
       have j1 := eq11 X0 X0
       grind)
    | exact resolve eq910 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq1844 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1835 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1845 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1844 X0
       have j1 := eq905 X0
       grind)
    | (have r₁ := eq1844 X0
       have r₂ := eq905 X0
       grind)
    | exact resolve eq1844 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1844
  have eq1860 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1874 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 x X0 X1 y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1882 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1885 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1882 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1882
    | exact resolve eq1882 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882
  have eq1890 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1860 X0 x x X3 X4
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1860
    | exact resolve eq1860 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1860
  have eq1899 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1885 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1885
    | (have j0 := eq1885 x y
       grind)
    | exact resolve eq1885 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6239 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq883
       grind)
    | exact superpose eq883 eq39
    | exact resolve eq39 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq6240 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6239
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6239
    | exact resolve eq6239 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6239
  have eq6244 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq6240
    | exact resolve eq6240 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6240
  have eq15214 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0 X0 x X0
       have i₂ := eq1890 X0 X0 x
       grind)
    | exact superpose eq1890 eq176
    | exact resolve eq176 eq1890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq15366 : x = (M.op (M.op (M.op x x) (M.op x y)) x) := by
    first
    | (have i₁ := eq1874 x x
       have i₂ := eq15214 x
       grind)
    | exact superpose eq15214 eq1874
    | exact resolve eq1874 eq15214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874
  have eq15369 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1890 X0 X0 X0
       have i₂ := eq15214 X0
       grind)
    | exact superpose eq15214 eq1890
    | exact resolve eq1890 eq15214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15383 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1890 (M.op X0 X0) X0 x
       have i₂ := eq15214 X0
       grind)
    | exact superpose eq15214 eq1890
    | exact resolve eq1890 eq15214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890 eq15214
  have eq15454 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq15369 X0
       grind)
    | exact superpose eq15369 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq15369 X0
       grind)
    | exact resolve eq13 eq15369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15463 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq15454 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15454
  have eq15480 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15463 X2 X0
       have i₂ := eq15463 X1 X0
       grind)
    | exact superpose eq15463 eq15463
    | exact resolve eq15463 eq15463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15504 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15369 X0
       have i₂ := eq15463 X1 (M.op X0 X0)
       grind)
    | exact superpose eq15463 eq15369
    | exact resolve eq15369 eq15463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15369
  have eq15722 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (σ (k (M.op X0 X0) (M.op X1 X1))) ∨ (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq915 (M.op X0 X0) X2
       have i₂ := eq15480 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq915 (M.op X0 X0) X2
       have i₂ := eq15480 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq15480 eq915
    | (have j0 := eq915 (M.op X0 X0) X2
       grind)
    | exact resolve eq915 eq15480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq15808 : ∀ X0 X2 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq15722 X0 x X2
       have i₂ := eq15504 X0 x
       grind)
    | exact superpose eq15504 eq15722
    | (have j0 := eq15722 X0 x X2
       grind)
    | exact resolve eq15722 eq15504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15722
  have eq15809 : ∀ X0 X2 : G, (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have j0 := eq15808 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15808
  have eq15958 : ∀ X0 : G, (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (M.op x y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 X0)
       have i₂ := eq15809 X0 sF1
       grind)
    | exact superpose eq15809 eq50
    | exact resolve eq50 eq15809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq15968 : ∀ X0 : G, (τ (M.op (σ x) (σ x))) = (k x (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (M.op X0 X0)
       have i₂ := eq15809 X0 sF2
       grind)
    | exact superpose eq15809 eq44
    | exact resolve eq44 eq15809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq15978 : ∀ X0 : G, (τ (M.op (σ y) (σ y))) = (k y (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op X0 X0)
       have i₂ := eq15809 X0 sF3
       grind)
    | exact superpose eq15809 eq47
    | exact resolve eq47 eq15809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq15996 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq15978 x
       have i₂ := eq15463 x y
       grind)
    | exact superpose eq15463 eq15978
    | exact resolve eq15978 eq15463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15978
  have eq16006 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq15968 x
       have i₂ := eq15463 x x
       grind)
    | exact superpose eq15463 eq15968
    | exact resolve eq15968 eq15463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15968
  have eq16016 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq15958 x
       have i₂ := eq15463 x sF0
       grind)
    | exact superpose eq15463 eq15958
    | exact resolve eq15958 eq15463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15958
  have eq16063 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq15996 eq14
    | exact resolve eq14 eq15996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16120 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq16006 eq14
    | exact resolve eq14 eq16006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16483 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16120
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq16120
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq16120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16120
  have eq16562 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq16483
  have eq16623 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16562
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq16562
    | exact resolve eq16562 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq16562
  have eq16660 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16623
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16623
    | exact resolve eq16623 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16623
  have eq17237 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6244 eq893
    | exact resolve eq893 eq6244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq17246 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq17237
       have r₂ := eq27
       grind)
    | exact resolve eq17237 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17237
  have eq17253 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16660 eq17246
    | exact resolve eq17246 eq16660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17246
  have eq17255 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16660 eq17253
    | exact resolve eq17253 eq16660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17253
  have eq17313 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17255 eq1845
    | (have j0 := eq1845 (σ x)
       grind)
    | exact resolve eq1845 eq17255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq17324 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq905 (σ x)
       grind)
    | (have r₁ := eq17313
       have r₂ := eq905 (σ x)
       grind)
    | exact resolve eq17313 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17313
  have eq17333 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6244 eq17324
    | exact resolve eq17324 eq6244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6244 eq17324
  have eq17337 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16660 eq17333
    | exact resolve eq17333 eq16660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16660 eq17333
  have eq17344 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17337 eq141
    | exact resolve eq141 eq17337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17337
  have eq17364 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq17344
    | exact resolve eq17344 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17344
  have eq17371 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq905 x
       grind)
    | (have r₁ := eq17364
       have r₂ := eq905 x
       grind)
    | exact resolve eq17364 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq17364
  have eq17405 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1885 x x
       have i₂ := eq17371
       grind)
    | exact superpose eq17371 eq1885
    | exact resolve eq1885 eq17371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17371
  have eq17411 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17405
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17405
    | exact resolve eq17405 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17405
  have eq17436 : x = (M.op (M.op x (M.op x y)) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15366
       have i₂ := eq17411
       grind)
    | exact superpose eq17411 eq15366
    | exact resolve eq15366 eq17411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15366
  have eq17477 : x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1899 eq17436
    | exact resolve eq17436 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899 eq17436
  have eq17513 : y = (M.op (M.op x x) y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17477 eq174
    | exact resolve eq174 eq17477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq17477
  have eq17528 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17411 eq17513
    | exact resolve eq17513 eq17411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17411 eq17513
  have eq17534 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17528
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17528
    | exact resolve eq17528 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17528
  have eq17535 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq17534
  have eq17536 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17535 eq28
    | exact resolve eq28 eq17535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq17535
  have eq17630 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq17536
    | exact resolve eq17536 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17536
  have eq17631 : y = (M.op x y) := by grind
  clear eq17630
  have eq17643 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq17631
       grind)
    | exact superpose eq17631 eq24
    | exact resolve eq24 eq17631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq17666 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq16063
       have i₂ := eq17631
       grind)
    | exact superpose eq17631 eq16063
    | exact resolve eq16063 eq17631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16063
  have eq17675 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq17643 eq20
    | exact resolve eq20 eq17643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17643
  have eq17940 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq17675 eq16016
    | exact resolve eq16016 eq17675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16016
  have eq18089 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq17666
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq17666
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq17666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18173 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq18089
  have eq18244 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq41 eq18173
    | exact resolve eq18173 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18173
  have eq18305 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq17675 eq18244
    | exact resolve eq18244 eq17675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18244
  have eq18345 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq18305
    | exact resolve eq18305 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18305
  have eq18370 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq17675 eq18345
    | exact resolve eq18345 eq17675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18345
  have eq20339 : (τ (k (σ y) (σ y))) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18370 eq17940
    | exact resolve eq17940 eq18370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17940 eq18370
  have eq20377 : (k y y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq115 eq20339
    | exact resolve eq20339 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20339
  have eq20379 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq20377
       have i₂ := eq17631
       grind)
    | exact superpose eq17631 eq20377
    | exact resolve eq20377 eq17631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20377
  have eq20381 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq20379
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq20379 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20379
  have eq20384 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20381 eq17666
    | exact resolve eq17666 eq20381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17666
  have eq20398 : ∀ X0 : G, (M.op X0 X0) = (k X0 (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20381 eq15463
    | exact resolve eq15463 eq20381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20400 : ∀ X0 X1 : G, (k X0 (k (M.op x y) (M.op x y))) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq20381 eq15480
    | exact resolve eq15480 eq20381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20407 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20381 eq15809
    | exact resolve eq15809 eq20381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15809 eq20381
  have eq20420 : ∀ X0 : G, (M.op X0 X0) = (k X0 (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq41 eq20407
    | exact resolve eq20407 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20407
  have eq20427 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq41 eq20384
    | exact resolve eq20384 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq20384
  have eq20430 : ∀ X0 : G, (M.op X0 X0) = (k X0 (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq17675 eq20420
    | exact resolve eq20420 eq17675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20420
  have eq20434 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq17675 eq20427
    | exact resolve eq20427 eq17675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20427
  have eq20437 : ∀ X0 : G, (M.op X0 X0) = (k X0 (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq20 eq20430
    | (have j0 := eq20430 X0
       grind)
    | exact resolve eq20430 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20430
  have eq20441 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq20434
    | exact resolve eq20434 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20434
  have eq20444 : ∀ X0 : G, (M.op X0 X0) = (k X0 (k (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq17675 eq20437
    | exact resolve eq20437 eq17675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20437
  have eq20448 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq17675 eq20441
    | exact resolve eq20441 eq17675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20441
  have eq20490 : ∀ X0 X1 : G, (k X0 (k (σ y) (σ y))) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq20448 eq15480
    | exact resolve eq15480 eq20448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15480
  have eq20493 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (k (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq20448 eq15504
    | exact resolve eq15504 eq20448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20494 : ∀ X0 : G, (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq20448 eq15504
    | exact resolve eq15504 eq20448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20448
  have eq20514 : (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq20494 x
       have i₂ := eq20400 (k sF3 sF3) x
       grind)
    | exact superpose eq20400 eq20494
    | exact resolve eq20494 eq20400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20494
  have eq20515 : ∀ X0 : G, (k X0 (k (M.op x y) (M.op x y))) = (k X0 (k (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq20490 X0 x
       have i₂ := eq20400 X0 x
       grind)
    | exact superpose eq20400 eq20490
    | exact resolve eq20490 eq20400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20490
  have eq20594 : ∀ X0 : G, (k X0 (k (M.op x y) (M.op x y))) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20398 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq20398
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq20398 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20606 : ∀ X0 X1 : G, (M.op (M.op (k X0 (k (M.op x y) (M.op x y))) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15383 X0 X1
       have i₂ := eq20398 X0
       grind)
    | exact superpose eq20398 eq15383
    | exact resolve eq15383 eq20398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15383
  have eq20615 : ∀ X0 X1 : G, (k X0 (k (M.op x y) (M.op x y))) = (k (k X0 (k (M.op x y) (M.op x y))) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15504 X0 X1
       have i₂ := eq20398 X0
       grind)
    | exact superpose eq20398 eq15504
    | exact resolve eq15504 eq20398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15504
  have eq20645 : ∀ X0 : G, (k (σ X0) (k (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq20398 eq344
    | exact resolve eq344 eq20398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20661 : ∀ X0 : G, (k X0 (k (M.op x y) (M.op x y))) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq20594 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20594
  have eq20674 : ∀ X0 : G, (k (σ X0) (k (σ y) (σ y))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq17675 eq20645
    | exact resolve eq20645 eq17675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20645
  have eq20684 : ∀ X0 : G, (k X0 (k (M.op x y) (M.op x y))) = (k (k X0 (k (M.op x y) (M.op x y))) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq20615 X0 x
       have i₂ := eq20400 (k X0 (k sF0 sF0)) x
       grind)
    | exact superpose eq20400 eq20615
    | exact resolve eq20615 eq20400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20400 eq20615
  have eq20703 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20515 eq20674
    | exact resolve eq20674 eq20515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20674
  have eq20935 : ∀ X0 : G, (k (τ X0) (k y y)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq20444 eq527
    | exact resolve eq527 eq20444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20444
  have eq20964 : ∀ X0 : G, (k (τ X0) (k (M.op x y) (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20935 X0
       have i₂ := eq17631
       grind)
    | exact superpose eq17631 eq20935
    | exact resolve eq20935 eq17631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20935
  have eq23141 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) (k y y)) := by
    intro X0
    first
    | exact superpose eq20493 eq527
    | exact resolve eq527 eq20493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20493
  have eq23145 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq23141 X0
       have i₂ := eq17631
       grind)
    | exact superpose eq17631 eq23141
    | exact resolve eq23141 eq17631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23141
  have eq23443 : ∀ X0 : G, (k (τ X0) (k y y)) = (τ (k X0 (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20515 eq527
    | exact resolve eq527 eq20515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq23538 : ∀ X0 : G, (k (τ X0) (k (M.op x y) (M.op x y))) = (τ (k X0 (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq23443 X0
       have i₂ := eq17631
       grind)
    | exact superpose eq17631 eq23443
    | exact resolve eq23443 eq17631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23443
  have eq23884 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (k X0 (τ (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20703 eq370
    | exact resolve eq370 eq20703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq23888 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq20703 eq20398
    | exact resolve eq20398 eq20703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23894 : ∀ X0 : G, (M.op X0 X0) = (k X0 (τ (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq23884 X0
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq23884
    | exact resolve eq23884 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23884
  have eq24436 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq23888 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq23888
    | exact resolve eq23888 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24766 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq23894 eq397
    | exact resolve eq397 eq23894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq23894
  have eq25209 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (τ X0) (τ X0))
       have i₂ := eq24436 X0
       grind)
    | exact superpose eq24436 eq15
    | exact resolve eq15 eq24436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27463 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (k (τ X0) (k (M.op x y) (M.op x y))) (k (τ X0) (k (M.op x y) (M.op x y))))) := by
    intro X0
    first
    | (have i₁ := eq24436 (M.op X0 X0)
       have i₂ := eq20964 X0
       grind)
    | exact superpose eq20964 eq24436
    | exact resolve eq24436 eq20964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24436
  have eq27469 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (σ (k (τ X0) (k (M.op x y) (M.op x y)))) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq27463 X0
       have i₂ := eq20703 (k (τ X0) (k sF0 sF0))
       grind)
    | exact superpose eq20703 eq27463
    | exact resolve eq27463 eq20703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20703 eq27463
  have eq27521 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (k (σ (τ X0)) (k (σ (M.op x y)) (σ (M.op x y)))) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq344 eq27469
    | exact resolve eq27469 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq27469
  have eq27555 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (k (σ (τ X0)) (k (σ y) (σ y))) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq17675 eq27521
    | exact resolve eq27521 eq17675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27521
  have eq27580 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (k (σ (τ X0)) (k (M.op x y) (M.op x y))) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20515 eq27555
    | exact resolve eq27555 eq20515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20515 eq27555
  have eq27598 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (σ (τ X0)) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20684 eq27580
    | exact resolve eq27580 eq20684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20684 eq27580
  have eq27608 : ∀ X0 : G, (k X0 (k (M.op x y) (M.op x y))) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27598 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq27598
    | exact resolve eq27598 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27598
  have eq27616 : ∀ X0 : G, (k X0 (k (M.op x y) (M.op x y))) = (k (M.op X0 X0) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq27608 X0
       have i₂ := eq20398 (M.op X0 X0)
       grind)
    | exact superpose eq20398 eq27608
    | exact resolve eq27608 eq20398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27608
  have eq53516 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op (k (σ y) (σ y)) (M.op (k (σ y) (σ y)) X0)) (k (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq20514 eq20606
    | exact resolve eq20606 eq20514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20606
  have eq53728 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op (k (σ y) (σ y)) X0) (k (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq53516 X0
       have i₂ := eq1885 (k sF3 sF3) (M.op (k sF3 sF3) X0)
       grind)
    | (have i₁ := eq53516 x
       have i₂ := eq1885 (k sF3 sF3) x
       grind)
    | exact superpose eq1885 eq53516
    | exact resolve eq53516 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885 eq53516
  have eq61140 : ∀ X0 : G, (M.op (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq53728 eq16
    | exact resolve eq16 eq53728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53728
  have eq61182 : ∀ X0 : G, (M.op (k (k (σ y) (σ y)) (k (M.op x y) (M.op x y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61140 X0
       have i₂ := eq20398 (k sF3 sF3)
       grind)
    | exact superpose eq20398 eq61140
    | exact resolve eq61140 eq20398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61140
  have eq61197 : ∀ X0 : G, (M.op (k (σ y) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq20514 eq61182
    | exact resolve eq61182 eq20514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20514 eq61182
  have eq61375 : ∀ X0 X1 : G, (M.op (M.op (M.op (k (σ y) (σ y)) X0) X1) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq61197 eq16
    | exact resolve eq16 eq61197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61393 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq61197 eq61375
    | exact resolve eq61375 eq61197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61197 eq61375
  have eq63445 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq61393 X0 X1
       grind)
    | exact superpose eq61393 eq16
    | exact resolve eq16 eq61393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63555 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63445 (σ X0) X1
       have i₂ := eq23888 X0
       grind)
    | exact superpose eq23888 eq63445
    | exact resolve eq63445 eq23888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23888 eq63445
  have eq64177 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq61393 (σ (M.op X1 X1)) X0
       have i₂ := eq63555 X1 X0
       grind)
    | exact superpose eq63555 eq61393
    | exact resolve eq61393 eq63555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61393
  have eq186864 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20398 (k sF0 sF0)
       have i₂ := eq20661 (k sF0 sF0)
       grind)
    | exact superpose eq20661 eq20398
    | (have j1 := eq20661 X0
       grind)
    | exact resolve eq20398 eq20661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20398 eq20661
  have eq187149 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq186864 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq186864 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq186864 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186864
  have eq187725 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15463 X0 X1
       have i₂ := eq187149 X0
       grind)
    | exact superpose eq187149 eq15463
    | exact resolve eq15463 eq187149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15463
  have eq187757 : ∀ X0 : G, (τ (k X0 X0)) = (k (τ (k X0 X0)) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq23145 X0
       have i₂ := eq187149 X0
       grind)
    | exact superpose eq187149 eq23145
    | exact resolve eq23145 eq187149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23145
  have eq187805 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63555 X0 X1
       have i₂ := eq187149 X0
       grind)
    | exact superpose eq187149 eq63555
    | exact resolve eq63555 eq187149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63555
  have eq187809 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq64177 X0 X0
       have i₂ := eq187149 X0
       grind)
    | exact superpose eq187149 eq64177
    | exact resolve eq64177 eq187149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64177
  have eq199742 : ∀ X0 X1 : G, (τ (k X0 (k (M.op x y) (M.op x y)))) = (k (τ X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24766 X0
       have i₂ := eq187725 X1 (τ X0)
       grind)
    | exact superpose eq187725 eq24766
    | exact resolve eq24766 eq187725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24766
  have eq199744 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25209 X0
       have i₂ := eq187725 X1 (τ X0)
       grind)
    | exact superpose eq187725 eq25209
    | exact resolve eq25209 eq187725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25209 eq187725
  have eq199984 : ∀ X0 X1 : G, (τ (k X0 X0)) = (k (τ X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq199744 X0 X1
       have i₂ := eq187149 X0
       grind)
    | exact superpose eq187149 eq199744
    | exact resolve eq199744 eq187149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199744
  have eq307646 : (τ (σ y)) = (k (τ (σ y)) (k (M.op x y) (M.op x y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17255 eq187757
    | exact resolve eq187757 eq17255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187757
  have eq307810 : (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20964 eq307646
    | exact resolve eq307646 eq20964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307646
  have eq307849 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15996 eq307810
    | exact resolve eq307810 eq15996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15996 eq307810
  have eq307861 : (τ (σ y)) = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq307849
       have i₂ := eq187149 y
       grind)
    | exact superpose eq187149 eq307849
    | exact resolve eq307849 eq187149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307849
  have eq307862 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq307861
       have i₂ := eq17631
       grind)
    | exact superpose eq17631 eq307861
    | exact resolve eq307861 eq17631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307861
  have eq307863 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31 eq307862
    | exact resolve eq307862 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq307862
  have eq307864 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq307863
       have i₂ := eq17631
       grind)
    | exact superpose eq17631 eq307863
    | exact resolve eq307863 eq17631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307863
  have eq307865 : y = (k x x) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq307864
       have i₂ := eq187149 x
       grind)
    | exact superpose eq187149 eq307864
    | exact resolve eq307864 eq187149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307864
  have eq307866 : (M.op x y) = (k x x) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq307865
       have i₂ := eq17631
       grind)
    | exact superpose eq17631 eq307865
    | exact resolve eq307865 eq17631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307865
  have eq307867 : x = (k x x) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq307866
       have i₂ := eq187149 x
       grind)
    | exact superpose eq187149 eq307866
    | exact resolve eq307866 eq187149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307866
  have eq321038 : ∀ X0 X1 : G, (τ (k X0 (k (M.op x y) (M.op x y)))) = (k (τ (M.op X0 X0)) (k X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq27616 eq199742
    | exact resolve eq199742 eq27616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27616 eq199742
  have eq321753 : ∀ X0 X1 : G, (τ (k X0 (k (M.op x y) (M.op x y)))) = (k (τ (k X0 X0)) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq321038 X0 X1
       have i₂ := eq187149 X0
       grind)
    | exact superpose eq187149 eq321038
    | exact resolve eq321038 eq187149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321038
  have eq321934 : ∀ X0 X1 : G, (k (τ X0) (k (M.op x y) (M.op x y))) = (k (τ (k X0 X0)) (k X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq23538 eq321753
    | exact resolve eq321753 eq23538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23538 eq321753
  have eq783159 : ∀ X0 : G, (k (τ (σ x)) (k (M.op x y) (M.op x y))) = (k (τ (σ y)) (k X0 X0)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq17255 eq321934
    | exact resolve eq321934 eq17255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17255 eq321934
  have eq783764 : (τ (k (σ y) (σ y))) = (k (τ (σ x)) (k (M.op x y) (M.op x y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq783159 x
       have i₂ := eq199984 sF3 x
       grind)
    | exact superpose eq199984 eq783159
    | exact resolve eq783159 eq199984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199984 eq783159
  have eq784001 : (τ (k (σ y) (σ y))) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20964 eq783764
    | exact resolve eq783764 eq20964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20964 eq783764
  have eq784123 : (τ (k (σ y) (σ y))) = (M.op x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16006 eq784001
    | exact resolve eq784001 eq16006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16006 eq784001
  have eq784178 : (k x x) = (τ (k (σ y) (σ y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq784123
       have i₂ := eq187149 x
       grind)
    | exact superpose eq187149 eq784123
    | exact resolve eq784123 eq187149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784123
  have eq784204 : (k x x) = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq115 eq784178
    | exact resolve eq784178 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq784178
  have eq784217 : (k x x) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq784204
       have i₂ := eq17631
       grind)
    | exact superpose eq17631 eq784204
    | exact resolve eq784204 eq17631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784204
  have eq784223 : y = (k x x) ∨ (k x x) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq784217
       have i₂ := eq187149 x
       grind)
    | exact superpose eq187149 eq784217
    | exact resolve eq784217 eq187149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784217
  have eq784226 : (M.op x y) = (k x x) ∨ (k x x) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq784223
       have i₂ := eq17631
       grind)
    | exact superpose eq17631 eq784223
    | exact resolve eq784223 eq17631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17631 eq784223
  have eq784227 : x = (k x x) ∨ (M.op x y) = (k x x) ∨ (k x x) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq784226
       have i₂ := eq187149 x
       grind)
    | exact superpose eq187149 eq784226
    | exact resolve eq784226 eq187149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187149 eq784226
  have eq784228 : x = (k x x) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq307867 eq784227
    | exact resolve eq784227 eq307867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307867 eq784227
  have eq784229 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by grind
  clear eq784228
  have eq904093 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq784229 eq141
    | exact resolve eq141 eq784229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq784229
  have eq904445 : x = (k x x) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq904093
    | exact resolve eq904093 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq904093
  have eq904446 : (M.op x y) = (k x x) ∨ x = (k x x) := by grind
  clear eq904445
  have eq904595 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq187809 x x
       have i₂ := eq904446
       grind)
    | exact superpose eq904446 eq187809
    | exact resolve eq187809 eq904446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187809 eq904446
  have eq904872 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq20 eq904595
    | (have j0 := eq904595 X0
       grind)
    | exact resolve eq904595 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq904595
  have eq904965 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq17675 eq904872
    | exact resolve eq904872 eq17675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904872
  have eq909898 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq904965 eq26
    | (have j1 := eq904965 (σ x)
       grind)
    | exact resolve eq26 eq904965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904965
  have eq911327 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq187805 x X0
       have i₂ := eq909898
       grind)
    | exact superpose eq909898 eq187805
    | exact resolve eq187805 eq909898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187805 eq909898
  have eq911617 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq911327 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq911327
    | (have j0 := eq911327 X0
       grind)
    | exact resolve eq911327 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq911327
  have eq915858 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq911617 eq26
    | (have j1 := eq911617 (σ y)
       grind)
    | exact resolve eq26 eq911617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq911617
  have eq916190 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq915858
  have eq916363 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq916190 eq27
    | exact resolve eq27 eq916190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq916190
  have eq916794 : False := by grind
  exact eq916794

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxx_y_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  clear eq18
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq74 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq77 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq71 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq71
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq77 (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq77
    | exact resolve eq77 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq77 X0 X0 x
       grind)
    | exact superpose eq77 eq52
    | exact resolve eq52 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq199 X0 X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq199
    | exact resolve eq199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq231 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq238 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq86 X0 X0
       grind)
    | exact superpose eq86 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq86 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq86 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq86 X0 X1
       grind)
    | exact resolve eq12 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq243 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq238 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq245 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq243 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq243 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq243 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq254 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq77 X0 X0 X0
       have i₂ := eq206 X0
       grind)
    | exact superpose eq206 eq77
    | exact resolve eq77 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq255 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X0 X0 X1
       have i₂ := eq206 X0
       grind)
    | exact superpose eq206 eq52
    | exact resolve eq52 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq206
  have eq272 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq9
    | exact resolve eq9 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq254 X0
       grind)
    | exact resolve eq12 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq277 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq76 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq272 X0 X1
       have i₂ := eq76 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq76 eq272
    | exact resolve eq272 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq562 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq277 X0 X1
       grind)
    | exact superpose eq277 eq9
    | exact resolve eq9 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 X1
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq562
    | exact resolve eq562 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq581 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq277 X1 X0
       have i₂ := eq570 X1 X0
       grind)
    | exact superpose eq570 eq277
    | exact resolve eq277 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq584 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X0
       have i₂ := eq570 X1 X0
       grind)
    | exact superpose eq570 eq9
    | exact resolve eq9 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq245 (M.op X0 X0) X1
       have i₂ := eq275 X0 (M.op X0 X0)
       grind)
    | exact superpose eq275 eq245
    | (have j0 := eq245 (M.op X0 X0) X1
       grind)
    | exact resolve eq245 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq671 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq651 X0 X1
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq651
    | (have j0 := eq651 X0 X1
       grind)
    | exact resolve eq651 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq651
  have eq672 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq671 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq866 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq570 X0 X2
       have i₂ := eq672 X1 X0
       grind)
    | exact superpose eq672 eq570
    | exact resolve eq570 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq880 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 (M.op X1 X1)
       have i₂ := eq672 X1 X0
       grind)
    | exact superpose eq672 eq23
    | exact resolve eq23 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq672
  have eq938 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq866 (σ X0) X1 X2
       have i₂ := eq15 X0 (M.op X1 X1)
       grind)
    | exact superpose eq15 eq866
    | exact resolve eq866 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq1147 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq938 X0 x X2
       have i₂ := eq275 x X0
       grind)
    | exact superpose eq275 eq938
    | exact resolve eq938 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq1235 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 (σ (M.op X1 X1))
       have i₂ := eq1147 X1 X0
       grind)
    | exact superpose eq1147 eq584
    | exact resolve eq584 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1673 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq880 X0 x
       have i₂ := eq275 x (τ X0)
       grind)
    | exact superpose eq275 eq880
    | exact resolve eq880 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq880
  have eq2244 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1673 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1673
    | exact resolve eq1673 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq2829 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq2244 X0
       grind)
    | exact superpose eq2244 eq11
    | exact resolve eq11 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq3307 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq231
       have i₂ := eq2829 y
       grind)
    | exact superpose eq2829 eq231
    | exact resolve eq231 eq2829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq3308 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3307
       have i₂ := eq2829 y
       grind)
    | exact superpose eq2829 eq3307
    | exact resolve eq3307 eq2829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2829 eq3307
  have eq3309 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3308
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq3308
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq3308 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3308
  have eq3310 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq3309
  have eq44706 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3310
       grind)
    | exact superpose eq3310 eq10
    | exact resolve eq10 eq3310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3310
  have eq44800 : y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44706
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq44706
    | exact resolve eq44706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44706
  have eq44801 : (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq44800
  have eq51826 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 (M.op (M.op X0 X0) X1)) (M.op X0 X2)) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X1) X0 (M.op X0 X2)
       have i₂ := eq216 X0 X0 X1 X2
       grind)
    | exact superpose eq216 eq9
    | exact resolve eq9 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq51890 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51826 X0 X1 X2
       have i₂ := eq570 X0 X1
       grind)
    | exact superpose eq570 eq51826
    | exact resolve eq51826 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51826
  have eq52273 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51890 (M.op (M.op X0 X0) (M.op X0 X1)) X2 X0
       have i₂ := eq255 X0 X1
       grind)
    | exact superpose eq255 eq51890
    | exact resolve eq51890 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq51890
  have eq52515 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52273 X0 X1 X2
       have i₂ := eq570 X0 (M.op X0 X1)
       grind)
    | exact superpose eq570 eq52273
    | exact resolve eq52273 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq52273
  have eq792085 : (M.op y y) = (τ (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq44801
       grind)
    | exact superpose eq44801 eq10
    | exact resolve eq10 eq44801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44801
  have eq792542 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq792085
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq792085
    | exact resolve eq792085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792085
  have eq792543 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq792542
  have eq793313 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq52515 y y X0
       have i₂ := eq792543
       grind)
    | exact superpose eq792543 eq52515
    | exact resolve eq52515 eq792543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52515 eq792543
  have eq793330 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq793313 X0
       have i₂ := eq584 X0 y
       grind)
    | exact superpose eq584 eq793313
    | exact resolve eq793313 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793313
  have eq793705 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1147 y X0
       have i₂ := eq793330 X1
       grind)
    | exact superpose eq793330 eq1147
    | (have j1 := eq793330 X1
       grind)
    | exact resolve eq1147 eq793330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147
  have eq793999 : ∀ X0 : G, x = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 y y
       have i₂ := eq793330 X0
       grind)
    | exact superpose eq793330 eq76
    | (have j1 := eq793330 x
       grind)
    | exact resolve eq76 eq793330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq793330
  have eq798929 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq793999 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793999
  have eq798930 : x = (M.op y x) := by grind
  clear eq798929
  have eq798965 : y = (M.op x y) := by
    first
    | (have i₁ := eq584 x y
       have i₂ := eq798930
       grind)
    | exact superpose eq798930 eq584
    | exact resolve eq584 eq798930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq798930
  have eq814614 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq793705 (σ y) X0
       grind)
    | exact superpose eq793705 eq16
    | (have j1 := eq793705 X0 X0
       grind)
    | exact resolve eq16 eq793705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793705
  have eq815838 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq814614 X0
       have i₂ := eq798965
       grind)
    | exact superpose eq798965 eq814614
    | (have j0 := eq814614 X0
       grind)
    | exact resolve eq814614 eq798965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798965 eq814614
  have eq815839 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq815838 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815838
  have eq815917 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq581 X0 y
       have i₂ := eq815839 y
       grind)
    | exact superpose eq815839 eq581
    | exact resolve eq581 eq815839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq815956 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1235 X0 y
       have i₂ := eq815839 y
       grind)
    | exact superpose eq815839 eq1235
    | exact resolve eq1235 eq815839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235 eq815839
  have eq833665 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq815956 (σ x)
       grind)
    | exact superpose eq815956 eq16
    | exact resolve eq16 eq815956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815956
  have eq834071 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq833665
       have i₂ := eq815917 x
       grind)
    | exact superpose eq815917 eq833665
    | exact resolve eq833665 eq815917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815917 eq833665
  have eq834072 : False := by grind
  exact eq834072
