import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) (τ X1)
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq48 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq49 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq52 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq49 X0 X2 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq49 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq58 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq78 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X2 X3) = (M.op X2 X3) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq48 X2 X3 X0
       grind)
    | exact superpose eq48 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq48 X1 X0 X1
       grind)
    | (have r₁ := eq13 X0 X2
       have r₂ := eq48 X0 X1 X2
       grind)
    | exact resolve eq13 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq48 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq87 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq86 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq90 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X2 X3) = (M.op X2 X3) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq78 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq87 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq87 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq87 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X2 X3) = (M.op X2 X3) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq90 X0 X1 X2 X3
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq90 X0 X0 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq90 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq91 (σ X0)
       grind)
    | exact superpose eq91 eq15
    | exact resolve eq15 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq91 (τ X0)
       grind)
    | exact superpose eq91 eq18
    | exact resolve eq18 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq99 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq99
    | exact resolve eq99 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq104 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq95
    | exact resolve eq95 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq100 X0
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq100
    | exact resolve eq100 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq100
  have eq188 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X0)) = (M.op X2 (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq52 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq52 eq15
    | (have j1 := eq52 (σ X0) X2 (σ X1)
       grind)
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq200 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq197 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq197 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq204 : ∀ X0 X1 X2 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X0)) = (M.op X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq188 X0 X1 X2
       have i₂ := eq104 X1
       grind)
    | exact superpose eq104 eq188
    | (have j0 := eq188 X0 X1 X2
       grind)
    | exact resolve eq188 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq217 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq217 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq217 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq217 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1347 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1354 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1347 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347
  have eq1379 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1354 X1 X0
       have i₂ := eq1354 X0 X1
       grind)
    | exact superpose eq1354 eq1354
    | (have j0 := eq1354 X1 X0
       have j1 := eq1354 X1 X0
       grind)
    | exact resolve eq1354 eq1354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1428 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq1354 (τ X0) X1
       grind)
    | exact superpose eq1354 eq18
    | (have j1 := eq1354 (τ X0) X1
       grind)
    | exact resolve eq18 eq1354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1431 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1354 (σ X0) (σ X1)
       grind)
    | exact superpose eq1354 eq15
    | (have j1 := eq1354 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq1354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1440 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq1354 (τ X0) (τ X1)
       grind)
    | exact superpose eq1354 eq31
    | (have j1 := eq1354 (τ X0) (τ X1)
       grind)
    | exact resolve eq31 eq1354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq1451 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1440 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1440
    | (have j0 := eq1440 X0 X1
       grind)
    | exact resolve eq1440 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1440
  have eq1454 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1431 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1431
    | (have j0 := eq1431 X0 X1
       grind)
    | exact resolve eq1431 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431
  have eq1469 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1379 X0 X1
       have j1 := eq200 X1 X0
       grind)
    | (have r₁ := eq1379 X0 X1
       have r₂ := eq200 X0 X1
       grind)
    | (have r₁ := eq1379 X1 X0
       have r₂ := eq200 X0 X1
       grind)
    | exact resolve eq1379 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq2143 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (M.op X0 X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq223 (τ X0) X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq223
    | (have j0 := eq223 (τ X0) X1
       grind)
    | exact resolve eq223 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq2156 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2143 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2143
    | (have j0 := eq2143 X0 X1
       grind)
    | exact resolve eq2143 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143
  have eq2161 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2156 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2156
    | (have j0 := eq2156 X0 X1
       grind)
    | exact resolve eq2156 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156
  have eq2857 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq3022 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2857 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2857
    | (have j0 := eq2857 X0 X0
       grind)
    | exact resolve eq2857 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857
  have eq3136 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq223 X0 X1
       have i₂ := eq3022 X2 X0
       grind)
    | exact superpose eq3022 eq223
    | (have j0 := eq223 X0 X1
       have j1 := eq3022 X2 X0
       grind)
    | exact resolve eq223 eq3022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022
  have eq3157 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3136 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3136
  have eq7873 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1428 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1428
    | exact resolve eq1428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq8025 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7873 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7873
    | (have j0 := eq7873 X0 X1
       grind)
    | exact resolve eq7873 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7873
  have eq12675 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X2 (σ X1)) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq204 X1 X0 X2
       grind)
    | exact superpose eq204 eq10
    | (have j1 := eq204 X1 X0 X2
       grind)
    | exact resolve eq10 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq12888 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X2 (σ X1)) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12675 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12675
    | (have j0 := eq12675 X0 X1 X2
       grind)
    | exact resolve eq12675 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12675
  have eq35979 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1451 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451
  have eq42463 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (k (σ X1) (σ X0))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35979 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq35979
    | exact resolve eq35979 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35979
  have eq42524 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (k (τ (σ X1)) X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq42463 X0 X1
       have i₂ := eq22 (σ X1) X0
       grind)
    | exact superpose eq22 eq42463
    | (have j0 := eq42463 X0 X1
       grind)
    | exact resolve eq42463 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq42463
  have eq42575 : ∀ X0 X1 : G, (k X1 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq42524 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq42524
    | (have j0 := eq42524 X0 X1
       grind)
    | exact resolve eq42524 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42524
  have eq42613 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq42575 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq42575
    | (have j0 := eq42575 X0 X1
       grind)
    | (have r₁ := eq42575 X1 X1
       have r₂ := eq10 (k X1 X1)
       grind)
    | exact resolve eq42575 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42575
  have eq42637 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42613 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq42613
    | (have j0 := eq42613 X0 X1
       grind)
    | exact resolve eq42613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42613
  have eq42648 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42637 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42637
    | (have j0 := eq42637 X0 X1
       grind)
    | exact resolve eq42637 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42637
  have eq42658 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42648 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq42648
    | (have j0 := eq42648 X0 X1
       grind)
    | exact resolve eq42648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42648
  have eq42727 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42658 X1 X0
       have i₂ := eq1469 X0 X1
       grind)
    | exact superpose eq1469 eq42658
    | (have j0 := eq42658 X1 X0
       have j1 := eq1469 X0 X1
       grind)
    | exact resolve eq42658 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq42869 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42727 X0 X1
       have j1 := eq200 X1 X0
       grind)
    | (have r₁ := eq42727 X0 X1
       have r₂ := eq200 X0 X1
       grind)
    | (have r₁ := eq42727 X1 X0
       have r₂ := eq200 X0 X1
       grind)
    | exact resolve eq42727 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq42727
  have eq49040 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1454 x y
       grind)
    | exact superpose eq1454 eq16
    | (have j1 := eq1454 x y
       grind)
    | exact resolve eq16 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq50398 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq49040
       have i₂ := eq8025 x y
       grind)
    | exact superpose eq8025 eq49040
    | (have j1 := eq8025 x y
       grind)
    | (have r₁ := eq49040
       have r₂ := eq8025 x y
       grind)
    | exact resolve eq49040 eq8025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8025 eq49040
  have eq50402 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq50398
  have eq51182 : (τ (σ (k x y))) = (k y (τ (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq58 (σ x) y
       have i₂ := eq50402
       grind)
    | exact superpose eq50402 eq58
    | (have j0 := eq58 (σ y) y
       grind)
    | exact resolve eq58 eq50402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq50402
  have eq51198 : (k y x) = (τ (σ (k x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq51182
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq51182
    | exact resolve eq51182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51182
  have eq51212 : (k y x) = (k x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq51198
       have i₂ := eq10 (k x y)
       grind)
    | exact superpose eq10 eq51198
    | exact resolve eq51198 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51198
  have eq51220 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq42658 x y
       grind)
    | (have r₁ := eq51212
       have r₂ := eq42658 y x
       grind)
    | (have r₁ := eq51212
       have r₂ := eq42658 x y
       grind)
    | exact resolve eq51212 eq42658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42658 eq51212
  have eq51228 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq51220
       have i₂ := eq104 y
       grind)
    | exact superpose eq104 eq51220
    | exact resolve eq51220 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51220
  have eq51233 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq51228
       have i₂ := eq104 x
       grind)
    | exact superpose eq104 eq51228
    | exact resolve eq51228 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq51228
  have eq82684 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq12888 y x X0
       grind)
    | exact superpose eq12888 eq16
    | (have j1 := eq12888 y x X0
       grind)
    | exact resolve eq16 eq12888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12888
  have eq83082 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq82684 X0
       have j1 := eq3157 x X0 y
       grind)
    | (have r₁ := eq82684 X0
       have r₂ := eq3157 x x y
       grind)
    | exact resolve eq82684 eq3157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3157 eq82684
  have eq83526 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq42869 X0 (σ x)
       have i₂ := eq83082 X0
       grind)
    | exact superpose eq83082 eq42869
    | (have j0 := eq42869 X0 (σ x)
       grind)
    | (have r₁ := eq42869 X0 (σ x)
       have r₂ := eq83082 X0
       grind)
    | exact resolve eq42869 eq83082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42869 eq83082
  have eq83568 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq83526 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83526
  have eq86422 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq83568 (σ X0)
       grind)
    | exact superpose eq83568 eq15
    | exact resolve eq15 eq83568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83568
  have eq107574 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86422 y
       grind)
    | exact superpose eq86422 eq16
    | exact resolve eq16 eq86422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86422
  have eq4001889 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq51233
       grind)
    | exact superpose eq51233 eq10
    | exact resolve eq10 eq51233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51233
  have eq4001890 : y = (M.op y y) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq4001889
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4001889
    | exact resolve eq4001889 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4001889
  have eq4001891 : (σ x) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq2161 y x
       grind)
    | (have r₁ := eq4001890
       have r₂ := eq2161 y x
       grind)
    | exact resolve eq4001890 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4001890
  have eq4011250 : (M.op x x) = (τ (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq4001891
       grind)
    | exact superpose eq4001891 eq10
    | exact resolve eq10 eq4001891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4001891
  have eq4011319 : x = (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq4011250
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4011250
    | exact resolve eq4011250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4011250
  have eq4011324 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq4011319
       have r₂ := eq12 x x
       grind)
    | exact resolve eq4011319 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4011319
  have eq4020560 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq107574
       have i₂ := eq4011324
       grind)
    | exact superpose eq4011324 eq107574
    | exact resolve eq107574 eq4011324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107574 eq4011324
  have eq4020610 : y = (M.op y y) := by grind
  clear eq4020560
  have eq4030035 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq223 y X0
       have i₂ := eq4020610
       grind)
    | exact superpose eq4020610 eq223
    | (have j0 := eq223 y X0
       grind)
    | exact resolve eq223 eq4020610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq4030040 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq2161 y X0
       have i₂ := eq4020610
       grind)
    | exact superpose eq4020610 eq2161
    | (have j0 := eq2161 y X0
       grind)
    | (have r₁ := eq2161 y x
       have r₂ := eq4020610
       grind)
    | exact resolve eq2161 eq4020610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161 eq4020610
  have eq4030065 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq4030040 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4030040
  have eq4030070 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq4030035 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4030035
  have eq4127672 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq4030070 (σ X0)
       grind)
    | exact superpose eq4030070 eq15
    | exact resolve eq15 eq4030070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4030070
  have eq4127956 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4127672 X0
       have i₂ := eq4030065 X0
       grind)
    | exact superpose eq4030065 eq4127672
    | exact resolve eq4127672 eq4030065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4030065 eq4127672
  have eq4303818 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4127956 x
       grind)
    | exact superpose eq4127956 eq16
    | (have r₁ := eq16
       have r₂ := eq4127956 x
       grind)
    | exact resolve eq16 eq4127956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4127956
  have eq4303906 : False := by grind
  exact eq4303906

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq41 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X1 X1) = X1 := by
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
  clear eq17
  have eq48 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq49 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq50 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq41 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq49 X0 X2 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq49 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq78 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X2 X3) = (M.op X3 X2) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq48 X2 X3 X0
       grind)
    | exact superpose eq48 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq48 X1 X0 X1
       grind)
    | (have r₁ := eq13 X0 X2
       have r₂ := eq48 X0 X1 X2
       grind)
    | exact resolve eq13 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq48 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq87 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq86 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq90 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X2 X3) = (M.op X3 X2) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq78 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq87 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq87 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq87 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X2 X3) = (M.op X3 X2) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq90 X0 X1 X2 X3
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq90 X0 X0 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq90 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq91 (σ X0)
       grind)
    | exact superpose eq91 eq15
    | exact resolve eq15 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq91 (τ X0)
       grind)
    | exact superpose eq91 eq18
    | exact resolve eq18 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq99 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq99
    | exact resolve eq99 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq104 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq95
    | exact resolve eq95 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq100 X0
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq100
    | exact resolve eq100 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq100
  have eq128 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (k (σ X0) X2) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq50 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq50 eq15
    | (have j1 := eq50 (σ X0) X2 (σ X1)
       grind)
    | exact resolve eq15 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq139 : ∀ X0 X1 X2 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128 X0 X1 X2
       have i₂ := eq104 X1
       grind)
    | exact superpose eq104 eq128
    | (have j0 := eq128 X0 X1 X2
       grind)
    | exact resolve eq128 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq188 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = (M.op (σ X1) X2) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq52 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq52 eq15
    | (have j1 := eq52 (σ X1) X2 (σ X0)
       grind)
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq200 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq197 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq197 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq204 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq188 X0 X1 X2
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq188
    | (have j0 := eq188 X0 X1 X2
       grind)
    | exact resolve eq188 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq216 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq217 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq217 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq217 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1348 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1355 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1348 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq1380 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1355 X0 X1
       have i₂ := eq1355 X1 X0
       grind)
    | exact superpose eq1355 eq1355
    | (have j0 := eq1355 X0 X1
       have j1 := eq1355 X0 X1
       grind)
    | exact resolve eq1355 eq1355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1432 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1355 (σ X1) (σ X0)
       grind)
    | exact superpose eq1355 eq15
    | (have j1 := eq1355 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq1355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1441 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq1355 (τ X1) (τ X0)
       grind)
    | exact superpose eq1355 eq31
    | (have j1 := eq1355 (τ X1) (τ X0)
       grind)
    | exact resolve eq31 eq1355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq1452 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1441 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq1441
    | (have j0 := eq1441 X0 X1
       grind)
    | exact resolve eq1441 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1441
  have eq1455 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1432 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1432
    | (have j0 := eq1432 X0 X1
       grind)
    | exact resolve eq1432 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq1471 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1380 X0 X1
       have j1 := eq200 X0 X1
       grind)
    | (have r₁ := eq1380 X0 X1
       have r₂ := eq200 X0 X1
       grind)
    | (have r₁ := eq1380 X1 X0
       have r₂ := eq200 X0 X1
       grind)
    | exact resolve eq1380 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380
  have eq1711 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1471 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2150 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (M.op X0 X0) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq223 (τ X0) X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq223
    | (have j0 := eq223 (τ X0) X1
       grind)
    | exact resolve eq223 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2163 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2150 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2150
    | (have j0 := eq2150 X0 X1
       grind)
    | exact resolve eq2150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150
  have eq2168 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2163 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2163
    | (have j0 := eq2163 X0 X1
       grind)
    | exact resolve eq2163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2163
  have eq2862 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | (have j0 := eq45 X0 X0
       grind)
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq3027 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2862 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2862
    | (have j0 := eq2862 X0 X0
       grind)
    | exact resolve eq2862 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862
  have eq3122 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ (k X0 X2)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216 X0 X1
       have i₂ := eq3027 X0 X2
       grind)
    | exact superpose eq3027 eq216
    | (have j0 := eq216 X0 X1
       have j1 := eq3027 X0 X2
       grind)
    | exact resolve eq216 eq3027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3141 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq223 X0 X1
       have i₂ := eq3027 X2 X0
       grind)
    | exact superpose eq3027 eq223
    | (have j0 := eq223 X0 X1
       have j1 := eq3027 X2 X0
       grind)
    | exact resolve eq223 eq3027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq3152 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (σ (k X1 (τ X0))) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq106 X0
       have i₂ := eq3027 X1 (τ X0)
       grind)
    | exact superpose eq3027 eq106
    | (have j1 := eq3027 X1 (τ X0)
       grind)
    | exact resolve eq106 eq3027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq3027
  have eq3162 : ∀ X0 X1 X2 : G, (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3141 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3141
  have eq3174 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ (k X0 X2)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3122 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3122
  have eq3181 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3152 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3152
    | (have j0 := eq3152 X0 X1
       grind)
    | exact resolve eq3152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3152
  have eq3231 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3181 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3181
    | (have j0 := eq3181 X0 X0
       grind)
    | exact resolve eq3181 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3181
  have eq11947 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) X2) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq139 X1 X0 X2
       grind)
    | exact superpose eq139 eq10
    | (have j1 := eq139 X1 X0 X2
       grind)
    | exact resolve eq10 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq12152 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) X2) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11947 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11947
    | (have j0 := eq11947 X0 X1 X2
       grind)
    | exact resolve eq11947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11947
  have eq12685 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq204 X0 X1 X2
       grind)
    | exact superpose eq204 eq10
    | (have j1 := eq204 X0 X1 X2
       grind)
    | exact resolve eq10 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq12898 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12685 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12685
    | (have j0 := eq12685 X0 X1 X2
       grind)
    | exact resolve eq12685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12685
  have eq35993 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1452 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35994 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (k X0 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1452 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452
  have eq37269 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (k (σ X1) (σ X0))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35993 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq35993
    | exact resolve eq35993 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35993
  have eq37329 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (k (τ (σ X1)) X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37269 X0 X1
       have i₂ := eq22 (σ X1) X0
       grind)
    | exact superpose eq22 eq37269
    | (have j0 := eq37269 X0 X1
       grind)
    | exact resolve eq37269 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37269
  have eq37380 : ∀ X0 X1 : G, (k X1 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37329 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq37329
    | (have j0 := eq37329 X0 X1
       grind)
    | exact resolve eq37329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37329
  have eq37418 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37380 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq37380
    | (have j0 := eq37380 X0 X1
       grind)
    | (have r₁ := eq37380 X1 X1
       have r₂ := eq10 (k X1 X1)
       grind)
    | exact resolve eq37380 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37380
  have eq37442 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq37418 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq37418
    | (have j0 := eq37418 X0 X1
       grind)
    | exact resolve eq37418 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37418
  have eq37453 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq37442 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37442
    | (have j0 := eq37442 X0 X1
       grind)
    | exact resolve eq37442 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37442
  have eq37463 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37453 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq37453
    | (have j0 := eq37453 X0 X1
       grind)
    | exact resolve eq37453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37453
  have eq38310 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq37463 X0 X1
       have i₂ := eq1471 X0 X1
       grind)
    | exact superpose eq1471 eq37463
    | (have j0 := eq37463 X1 X0
       have j1 := eq1471 X1 X0
       grind)
    | exact resolve eq37463 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37463
  have eq38460 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38310 X0 X1
       have j1 := eq1711 X1 X0
       grind)
    | (have r₁ := eq38310 X0 X1
       have r₂ := eq1711 X0 X1
       grind)
    | (have r₁ := eq38310 X1 X0
       have r₂ := eq1711 X0 X1
       grind)
    | exact resolve eq38310 eq1711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1711 eq38310
  have eq39352 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38460 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq38460
    | (have j0 := eq38460 (σ X0) (σ X1)
       grind)
    | exact resolve eq38460 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38460
  have eq39424 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39352 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq39352
    | (have j0 := eq39352 X0 X1
       grind)
    | exact resolve eq39352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39352
  have eq42409 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (k (σ X1) (σ X0))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35994 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq35994
    | exact resolve eq35994 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35994
  have eq42589 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (k (τ (σ X1)) X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq42409 X0 X1
       have i₂ := eq22 (σ X1) X0
       grind)
    | exact superpose eq22 eq42409
    | (have j0 := eq42409 X0 X1
       grind)
    | exact resolve eq42409 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq42409
  have eq42638 : ∀ X0 X1 : G, (k X1 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq42589 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq42589
    | (have j0 := eq42589 X0 X1
       grind)
    | exact resolve eq42589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42589
  have eq42667 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq42638 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq42638
    | (have j0 := eq42638 X0 X1
       grind)
    | (have r₁ := eq42638 X1 X1
       have r₂ := eq10 (k X1 X1)
       grind)
    | exact resolve eq42638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42638
  have eq42678 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42667 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42667
    | (have j0 := eq42667 X0 X1
       grind)
    | exact resolve eq42667 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42667
  have eq42688 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42678 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq42678
    | (have j0 := eq42678 X0 X1
       grind)
    | exact resolve eq42678 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42678
  have eq42698 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42688 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq42688
    | (have j0 := eq42688 X0 X1
       grind)
    | exact resolve eq42688 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42688
  have eq42774 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42698 X0 X1
       have i₂ := eq1471 X0 X1
       grind)
    | exact superpose eq1471 eq42698
    | (have j0 := eq42698 X0 X1
       have j1 := eq1471 X0 X1
       grind)
    | exact resolve eq42698 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471 eq42698
  have eq42934 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42774 X0 X1
       have j1 := eq200 X0 X1
       grind)
    | (have r₁ := eq42774 X1 X0
       have r₂ := eq200 X0 X1
       grind)
    | (have r₁ := eq42774 X0 X1
       have r₂ := eq200 X0 X1
       grind)
    | exact resolve eq42774 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq42774
  have eq49128 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1455 x y
       grind)
    | exact superpose eq1455 eq16
    | (have j1 := eq1455 x y
       grind)
    | exact resolve eq16 eq1455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455
  have eq61387 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0
       have i₂ := eq3231 (σ X0) X1
       grind)
    | exact superpose eq3231 eq104
    | (have j1 := eq3231 (σ X0) X1
       grind)
    | exact resolve eq104 eq3231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3231
  have eq61645 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61387 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61387
    | (have j0 := eq61387 X0 X1
       grind)
    | exact resolve eq61387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61387
  have eq61783 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61645 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq61645
    | (have j0 := eq61645 X0 X1
       grind)
    | exact resolve eq61645 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61645
  have eq81232 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq12152 y x X0
       grind)
    | exact superpose eq12152 eq16
    | (have j1 := eq12152 y x X0
       grind)
    | exact resolve eq16 eq12152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12152
  have eq81628 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq81232 X0
       have j1 := eq3174 x X0 y
       grind)
    | (have r₁ := eq81232 X0
       have r₂ := eq3174 x x y
       grind)
    | exact resolve eq81232 eq3174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3174 eq81232
  have eq82049 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq42934 X0 (σ x)
       have i₂ := eq81628 X0
       grind)
    | exact superpose eq81628 eq42934
    | (have j0 := eq42934 X0 (σ x)
       grind)
    | (have r₁ := eq42934 X0 (σ x)
       have r₂ := eq81628 X0
       grind)
    | exact resolve eq42934 eq81628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81628
  have eq82085 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq82049 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82049
  have eq82640 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x x) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq12898 x y X0
       grind)
    | exact superpose eq12898 eq16
    | (have j1 := eq12898 x y X0
       grind)
    | exact resolve eq16 eq12898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12898
  have eq83036 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq82640 X0
       have j1 := eq3162 y X0 x
       grind)
    | (have r₁ := eq82640 X0
       have r₂ := eq3162 y x x
       grind)
    | exact resolve eq82640 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162 eq82640
  have eq83475 : ∀ X0 : G, (M.op (σ y) X0) ≠ (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq42934 (σ y) X0
       have i₂ := eq83036 X0
       grind)
    | exact superpose eq83036 eq42934
    | (have j0 := eq42934 (σ y) X0
       grind)
    | (have r₁ := eq42934 (σ y) X0
       have r₂ := eq83036 X0
       grind)
    | exact resolve eq42934 eq83036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42934 eq83036
  have eq83517 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq83475 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83475
  have eq84898 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq82085 (σ X0)
       grind)
    | exact superpose eq82085 eq15
    | exact resolve eq15 eq82085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82085
  have eq86346 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq83517 (σ X0)
       grind)
    | exact superpose eq83517 eq15
    | exact resolve eq15 eq83517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83517
  have eq106534 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84898 y
       grind)
    | exact superpose eq84898 eq16
    | exact resolve eq16 eq84898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84898
  have eq107619 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86346 x
       grind)
    | exact superpose eq86346 eq16
    | exact resolve eq16 eq86346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86346
  have eq1895507 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq218 X0 X1
       grind)
    | exact superpose eq218 eq10
    | (have j1 := eq218 X0 X1
       grind)
    | exact resolve eq10 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1895517 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1895507 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1895507
    | (have j0 := eq1895507 X0 X1
       grind)
    | exact resolve eq1895507 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895507
  have eq1900970 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1895517 X0 (σ X1)
       grind)
    | exact superpose eq1895517 eq15
    | (have j1 := eq1895517 X0 X0
       grind)
    | exact resolve eq15 eq1895517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895517
  have eq1900985 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1900970 X0 X1
       have i₂ := eq104 X1
       grind)
    | exact superpose eq104 eq1900970
    | (have j0 := eq1900970 X0 X1
       grind)
    | exact resolve eq1900970 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq1900970
  have eq5699203 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1900985 x y
       grind)
    | exact superpose eq1900985 eq16
    | (have j1 := eq1900985 x y
       grind)
    | exact resolve eq16 eq1900985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900985
  have eq5699204 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq61783 y x
       grind)
    | (have r₁ := eq5699203
       have r₂ := eq61783 y x
       grind)
    | exact resolve eq5699203 eq61783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61783 eq5699203
  have eq5711741 : (M.op y y) = (τ (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq5699204
       grind)
    | exact superpose eq5699204 eq10
    | exact resolve eq10 eq5699204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5699204
  have eq5711812 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5711741
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5711741
    | exact resolve eq5711741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5711741
  have eq5726114 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq5711812
       grind)
    | exact superpose eq5711812 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq5711812
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq5711812
       grind)
    | exact resolve eq12 eq5711812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5711812
  have eq5726143 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq5726114 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5726114
  have eq5740664 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq107619
       have i₂ := eq5726143 x
       grind)
    | exact superpose eq5726143 eq107619
    | exact resolve eq107619 eq5726143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107619 eq5726143
  have eq5740719 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq5740664
  have eq5740720 : x = (M.op x x) := by grind
  clear eq5740719
  have eq5740750 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq5740720
       grind)
    | exact superpose eq5740720 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq5740720
       grind)
    | exact resolve eq12 eq5740720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5740752 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq216 x X0
       have i₂ := eq5740720
       grind)
    | exact superpose eq5740720 eq216
    | (have j0 := eq216 x X0
       grind)
    | exact resolve eq216 eq5740720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq5740758 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2168 x X0
       have i₂ := eq5740720
       grind)
    | exact superpose eq5740720 eq2168
    | (have j0 := eq2168 x X0
       grind)
    | (have r₁ := eq2168 x x
       have r₂ := eq5740720
       grind)
    | exact resolve eq2168 eq5740720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5740720
  have eq5740783 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq5740758 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5740758
  have eq5740789 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq5740752 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5740752
  have eq5740791 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq5740750 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5740750
  have eq5741332 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq49128
       have i₂ := eq5740783 y
       grind)
    | exact superpose eq5740783 eq49128
    | exact resolve eq49128 eq5740783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49128
  have eq5741337 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq106534
       have i₂ := eq5740783 y
       grind)
    | exact superpose eq5740783 eq106534
    | exact resolve eq106534 eq5740783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106534
  have eq5741353 : y = (M.op y y) := by grind
  clear eq5741337
  have eq5741354 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq5741332
  have eq5741361 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq5741354
       have i₂ := eq5740791 y
       grind)
    | exact superpose eq5740791 eq5741354
    | exact resolve eq5741354 eq5740791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5741354
  have eq5758473 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq2168 y X0
       have i₂ := eq5741353
       grind)
    | exact superpose eq5741353 eq2168
    | (have j0 := eq2168 y X0
       grind)
    | (have r₁ := eq2168 y x
       have r₂ := eq5741353
       grind)
    | exact resolve eq2168 eq5741353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168 eq5741353
  have eq5758498 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq5758473 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5758473
  have eq5779463 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq5740789 (σ X0)
       grind)
    | exact superpose eq5740789 eq15
    | exact resolve eq15 eq5740789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5740789
  have eq5779728 : ∀ X0 : G, (σ (M.op X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq5779463 X0
       have i₂ := eq5740791 X0
       grind)
    | exact superpose eq5740791 eq5779463
    | exact resolve eq5779463 eq5740791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5740791 eq5779463
  have eq5795536 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5741361
       grind)
    | exact superpose eq5741361 eq16
    | exact resolve eq16 eq5741361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5795609 : (σ (k x y)) ≠ (σ (M.op y x)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq39424 x y
       have i₂ := eq5741361
       grind)
    | exact superpose eq5741361 eq39424
    | (have j0 := eq39424 x y
       grind)
    | exact resolve eq39424 eq5741361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39424 eq5741361
  have eq5795669 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq5795609
       have i₂ := eq5758498 x
       grind)
    | exact superpose eq5758498 eq5795609
    | exact resolve eq5795609 eq5758498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5758498 eq5795609
  have eq5795670 : (σ (k y x)) = (M.op (σ y) (σ x)) := by grind
  clear eq5795669
  have eq5795684 : (σ (k y x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq5795670
       have i₂ := eq5779728 y
       grind)
    | exact superpose eq5779728 eq5795670
    | exact resolve eq5795670 eq5779728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5779728 eq5795670
  have eq5795691 : (σ (M.op x y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq5795684
       have i₂ := eq5740783 y
       grind)
    | exact superpose eq5740783 eq5795684
    | exact resolve eq5795684 eq5740783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5740783 eq5795684
  have eq5795697 : False := by grind
  exact eq5795697

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq41 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq42 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq59 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq60 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq59 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq183 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0
       have i₂ := eq40 X0 X1
       grind)
    | (have i₁ := eq60 X0
       have i₂ := eq40 X0 (M.op X0 X0)
       grind)
    | exact superpose eq40 eq60
    | (have j1 := eq40 X1 X0
       grind)
    | exact resolve eq60 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq195 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq183 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq319 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq195 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq320 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq319 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq391 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq320 (σ X0)
       grind)
    | exact superpose eq320 eq15
    | exact resolve eq15 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq391 X0
       have i₂ := eq320 X0
       grind)
    | exact superpose eq320 eq391
    | exact resolve eq391 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq391
  have eq493 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq10
    | (have j1 := eq41 X0 X1
       grind)
    | exact resolve eq10 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq549 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X1
       have i₂ := eq398 X0
       grind)
    | exact superpose eq398 eq493
    | (have j0 := eq493 X0 X1
       grind)
    | exact resolve eq493 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq622 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq549 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq549
    | (have j0 := eq549 X0 X1
       grind)
    | exact resolve eq549 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq666 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq622 X0 X1
       have i₂ := eq398 X1
       grind)
    | exact superpose eq398 eq622
    | (have j0 := eq622 X0 X1
       grind)
    | exact resolve eq622 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq930 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq936 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq60 (σ X0)
       have i₂ := eq398 X0
       grind)
    | exact superpose eq398 eq60
    | exact resolve eq60 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq941 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq936 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq936
    | exact resolve eq936 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq943 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq930 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq930
    | exact resolve eq930 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq951 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq941 X0
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq941
    | exact resolve eq941 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq941
  have eq953 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq943
  have eq5193 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq666 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq666 X0 X1
       grind)
    | exact superpose eq666 eq10
    | (have j1 := eq666 X0 X1
       grind)
    | exact resolve eq10 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq5402 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5193 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5193
    | (have j0 := eq5193 X0 X1
       grind)
    | exact resolve eq5193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5193
  have eq6808 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42
    | exact resolve eq42 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq7206 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6808 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6808
    | (have j0 := eq6808 X0 X1
       grind)
    | exact resolve eq6808 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6808
  have eq142293 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5402 x y
       grind)
    | exact superpose eq5402 eq16
    | (have j1 := eq5402 x y
       grind)
    | exact resolve eq16 eq5402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5402
  have eq142469 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq7206 x y
       grind)
    | (have r₁ := eq142293
       have r₂ := eq7206 y x
       grind)
    | exact resolve eq142293 eq7206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7206 eq142293
  have eq146243 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq951 y
       have i₂ := eq142469
       grind)
    | exact superpose eq142469 eq951
    | exact resolve eq951 eq142469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951 eq142469
  have eq146280 : y = (M.op x x) := by
    first
    | (have r₁ := eq146243
       have r₂ := eq16
       grind)
    | exact resolve eq146243 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146243
  have eq149062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq953 x
       have i₂ := eq146280
       grind)
    | exact superpose eq146280 eq953
    | exact resolve eq953 eq146280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq146280
  have eq149097 : False := by grind
  exact eq149097

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq42 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq60 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq59 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq182 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0
       have i₂ := eq40 X0 X1
       grind)
    | (have i₁ := eq60 X0
       have i₂ := eq40 X0 (M.op X0 X0)
       grind)
    | exact superpose eq40 eq60
    | (have j1 := eq40 X1 X0
       grind)
    | exact resolve eq60 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq194 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq182 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq316 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq194 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq317 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq316 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq384 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq317 (σ X0)
       grind)
    | exact superpose eq317 eq15
    | exact resolve eq15 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq384 X0
       have i₂ := eq317 X0
       grind)
    | exact superpose eq317 eq384
    | exact resolve eq384 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq384
  have eq486 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq10
    | (have j1 := eq41 X1 X0
       grind)
    | exact resolve eq10 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq542 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq486 X0 X1
       have i₂ := eq391 X0
       grind)
    | exact superpose eq391 eq486
    | (have j0 := eq486 X0 X1
       grind)
    | exact resolve eq486 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq615 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq542 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq542
    | (have j0 := eq542 X0 X1
       grind)
    | exact resolve eq542 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq659 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq615 X0 X1
       have i₂ := eq391 X1
       grind)
    | exact superpose eq391 eq615
    | (have j0 := eq615 X0 X1
       grind)
    | exact resolve eq615 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq919 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq925 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq60 (σ X0)
       have i₂ := eq391 X0
       grind)
    | exact superpose eq391 eq60
    | exact resolve eq60 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq930 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq925 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq925
    | exact resolve eq925 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq932 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq919 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq919
    | exact resolve eq919 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq940 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq930 X0
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq930
    | exact resolve eq930 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq930
  have eq942 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq932
  have eq5180 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq659 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq659 X0 X1
       grind)
    | exact superpose eq659 eq10
    | (have j1 := eq659 X0 X1
       grind)
    | exact resolve eq10 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq5387 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5180 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5180
    | (have j0 := eq5180 X0 X1
       grind)
    | exact resolve eq5180 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5180
  have eq6769 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42
    | exact resolve eq42 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq7216 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6769 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6769
    | (have j0 := eq6769 X0 X1
       grind)
    | exact resolve eq6769 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6769
  have eq141711 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5387 y x
       grind)
    | exact superpose eq5387 eq16
    | (have j1 := eq5387 y x
       grind)
    | exact resolve eq16 eq5387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5387
  have eq141887 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq7216 x y
       grind)
    | (have r₁ := eq141711
       have r₂ := eq7216 x y
       grind)
    | exact resolve eq141711 eq7216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7216 eq141711
  have eq145666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq942 y
       have i₂ := eq141887
       grind)
    | exact superpose eq141887 eq942
    | exact resolve eq942 eq141887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942 eq141887
  have eq145702 : y = (M.op x x) := by
    first
    | (have r₁ := eq145666
       have r₂ := eq16
       grind)
    | exact resolve eq145666 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145666
  have eq148483 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq940 x
       have i₂ := eq145702
       grind)
    | exact superpose eq145702 eq940
    | exact resolve eq940 eq145702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940 eq145702
  have eq148519 : False := by grind
  exact eq148519

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxx_pyy_pxy_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23 (σ X0)
       grind)
    | exact superpose eq23 eq15
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq23 (τ X0)
       grind)
    | exact superpose eq23 eq17
    | exact resolve eq17 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq25
    | exact resolve eq25 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq27
    | exact resolve eq27 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq27
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq65 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq66 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq68 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq63 X1 X0
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq63 X0 X0
       have r₂ := eq61 X0 X0
       grind)
    | exact resolve eq63 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq63
  have eq71 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq73 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq103 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq65 X1 (τ X0)
       grind)
    | exact superpose eq65 eq17
    | (have j1 := eq65 X1 (τ X0)
       grind)
    | exact resolve eq17 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq157 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq148
    | (have j0 := eq148 X0 X1
       grind)
    | exact resolve eq148 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq166 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 X1
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq157
    | (have j0 := eq157 X0 X1
       grind)
    | exact resolve eq157 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq68
    | (have j0 := eq68 (σ X0) (σ X1)
       grind)
    | exact resolve eq68 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq68 X1 (τ X0)
       grind)
    | exact superpose eq68 eq18
    | (have j1 := eq68 X1 (τ X0)
       grind)
    | exact resolve eq18 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq234 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq68 (τ X0) X1
       grind)
    | exact superpose eq68 eq17
    | (have j1 := eq68 (τ X0) X1
       grind)
    | exact resolve eq17 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq249 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq231 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq231
    | (have j0 := eq231 X0 X1
       grind)
    | exact resolve eq231 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq256 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq210
    | (have j0 := eq210 X0 X1
       grind)
    | exact resolve eq210 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq262 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq249 X0 X1
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq249
    | (have j0 := eq249 X0 X1
       grind)
    | exact resolve eq249 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq266 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq256 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq256
    | (have j0 := eq256 X0 X1
       grind)
    | exact resolve eq256 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq349 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq558 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq71 X0 X1
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq610 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq558 X0 X1
       have j1 := eq103 X1 (σ X0)
       grind)
    | (have r₁ := eq558 X0 X0
       have r₂ := eq103 X0 (σ X0)
       grind)
    | (have r₁ := eq558 X0 X0
       have r₂ := eq103 X0 (σ X0)
       grind)
    | exact resolve eq558 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq558
  have eq662 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq610 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq610
    | (have j0 := eq610 X0 X1
       grind)
    | exact resolve eq610 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq696 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq662 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq662
    | (have j0 := eq662 X0 X1
       grind)
    | exact resolve eq662 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq716 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq696 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq696
    | (have j0 := eq696 X0 X1
       grind)
    | exact resolve eq696 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq2843 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq166 X0 X1
       grind)
    | exact superpose eq166 eq11
    | (have j1 := eq166 X0 X1
       grind)
    | exact resolve eq11 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq3652 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq234 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq234
    | exact resolve eq234 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq3836 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3652 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3652
    | (have j0 := eq3652 X0 X1
       grind)
    | exact resolve eq3652 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3652
  have eq4122 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq349 X0 X1
       have i₂ := eq262 X0 X1
       grind)
    | exact superpose eq262 eq349
    | (have j0 := eq349 X0 X1
       have j1 := eq262 X0 X1
       grind)
    | (have r₁ := eq349 X0 X1
       have r₂ := eq262 X0 X1
       grind)
    | exact resolve eq349 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq349
  have eq4228 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4122 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4122
  have eq7834 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq716 (τ X1) (τ X0)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq716
    | (have j0 := eq716 (τ X0) (τ X1)
       grind)
    | exact resolve eq716 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq7909 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7834 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7834
    | (have j0 := eq7834 X0 X1
       grind)
    | exact resolve eq7834 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7834
  have eq7934 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7909 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq7909
    | (have j0 := eq7909 X0 X1
       grind)
    | exact resolve eq7909 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7909
  have eq7955 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7934 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7934
    | (have j0 := eq7934 X0 X1
       grind)
    | exact resolve eq7934 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7934
  have eq7966 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7955 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7955
    | (have j0 := eq7955 X0 X1
       grind)
    | exact resolve eq7955 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7955
  have eq7973 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7966 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7966
    | (have j0 := eq7966 X0 X1
       grind)
    | exact resolve eq7966 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7966
  have eq7976 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7973 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7973
    | (have j0 := eq7973 X0 X1
       grind)
    | exact resolve eq7973 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7973
  have eq7977 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7976 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7976
    | (have j0 := eq7976 X0 X1
       grind)
    | exact resolve eq7976 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7976
  have eq9717 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq266 X0 X1
       grind)
    | exact superpose eq266 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq266 X0 X1
       grind)
    | exact resolve eq13 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq9760 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9717 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq9717
    | (have j0 := eq9717 X0 X1
       grind)
    | exact resolve eq9717 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9717
  have eq9875 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9760 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq9760
    | (have j0 := eq9760 X0 X1
       grind)
    | exact resolve eq9760 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9760
  have eq9876 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq9875 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9875
  have eq9957 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9876 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq9876
    | (have j0 := eq9876 X0 X1
       grind)
    | exact resolve eq9876 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9876
  have eq9988 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9957 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9957
    | (have j0 := eq9957 X0 X1
       grind)
    | exact resolve eq9957 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9957
  have eq9989 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq9988 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9988
  have eq107627 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq4228 X1 (τ X0)
       grind)
    | exact superpose eq4228 eq17
    | (have j1 := eq4228 X1 (τ X0)
       grind)
    | exact resolve eq17 eq4228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq107666 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq4228 (σ X0) X1
       grind)
    | exact superpose eq4228 eq22
    | (have j1 := eq4228 (σ X0) X1
       grind)
    | exact resolve eq22 eq4228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228
  have eq107676 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq107666 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq107666
    | (have j0 := eq107666 X0 X1
       grind)
    | exact resolve eq107666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107666
  have eq107685 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107627 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq107627
    | (have j0 := eq107627 X0 X1
       grind)
    | exact resolve eq107627 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107627
  have eq107707 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq107676 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq107676
    | (have j0 := eq107676 X0 X1
       grind)
    | exact resolve eq107676 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107676
  have eq107712 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107685 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq107685
    | (have j0 := eq107685 X0 X1
       grind)
    | exact resolve eq107685 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq107685
  have eq107729 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq107707 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq107707
    | (have j0 := eq107707 X0 X1
       grind)
    | exact resolve eq107707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107707
  have eq107734 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107712 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq107712
    | (have j0 := eq107712 X0 X1
       grind)
    | exact resolve eq107712 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107712
  have eq107744 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq107729 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq107729
    | (have j0 := eq107729 X0 X1
       grind)
    | exact resolve eq107729 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107729
  have eq107747 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq107734 X0 X1
       have i₂ := eq73 X1 X0
       grind)
    | exact superpose eq73 eq107734
    | (have j0 := eq107734 X0 X1
       grind)
    | exact resolve eq107734 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq107734
  have eq107751 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq107744 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq107744
    | (have j0 := eq107744 X0 X1
       grind)
    | exact resolve eq107744 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107744
  have eq110388 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq107751 (σ X0) X1
       grind)
    | exact superpose eq107751 eq22
    | (have j1 := eq107751 (σ X0) X1
       grind)
    | exact resolve eq22 eq107751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107751
  have eq110485 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq110388 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq110388
    | (have j0 := eq110388 X0 X1
       grind)
    | exact resolve eq110388 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110388
  have eq110614 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq110485 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq110485
    | (have j0 := eq110485 X0 X1
       grind)
    | exact resolve eq110485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110485
  have eq120715 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7977 X0 X1
       have i₂ := eq107747 X0 X1
       grind)
    | exact superpose eq107747 eq7977
    | (have j0 := eq7977 X1 X0
       have j1 := eq107747 X1 X0
       grind)
    | (have r₁ := eq7977 X0 X1
       have r₂ := eq107747 X0 X1
       grind)
    | (have r₁ := eq7977 X1 X1
       have r₂ := eq107747 X1 X1
       grind)
    | exact resolve eq7977 eq107747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120818 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq107747 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107747
  have eq120833 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq120715 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120715
  have eq120934 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq120833 X0 X1
       have j1 := eq120818 X1 X0
       grind)
    | (have r₁ := eq120833 X0 X1
       have r₂ := eq120818 X0 X1
       grind)
    | (have r₁ := eq120833 X1 X0
       have r₂ := eq120818 X0 X1
       grind)
    | (have r₁ := eq120833 X0 X0
       have r₂ := eq120818 X0 X0
       grind)
    | exact resolve eq120833 eq120818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120818 eq120833
  have eq138623 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (τ (k X1 (σ X0))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq120934 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120934
    | (have j0 := eq120934 (σ X0) X1
       grind)
    | exact resolve eq120934 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120934
  have eq138677 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq138623 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq138623
    | (have j0 := eq138623 X0 X1
       grind)
    | exact resolve eq138623 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq138623
  have eq185274 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X1)
       have i₂ := eq110614 X1 (σ X0)
       grind)
    | exact superpose eq110614 eq38
    | (have j1 := eq110614 X1 (σ X0)
       grind)
    | exact resolve eq38 eq110614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110614
  have eq185323 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq185274 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq185274
    | (have j0 := eq185274 X0 X1
       grind)
    | exact resolve eq185274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185274
  have eq185348 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq185323 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq185323
    | (have j0 := eq185323 X0 X1
       grind)
    | exact resolve eq185323 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185323
  have eq185365 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq185348 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq185348
    | (have j0 := eq185348 X0 X1
       grind)
    | exact resolve eq185348 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185348
  have eq185378 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq185365 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq185365
    | (have j0 := eq185365 X0 X1
       grind)
    | exact resolve eq185365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185365
  have eq185383 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq185378 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq185378
    | (have j0 := eq185378 X0 X1
       grind)
    | exact resolve eq185378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185378
  have eq195007 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op y y) = (k x y) ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq185383 x y
       grind)
    | exact superpose eq185383 eq16
    | (have j1 := eq185383 x y
       grind)
    | exact resolve eq16 eq185383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185383
  have eq199803 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq195007
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq195007
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq195007 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199808 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k x y) ∨ (M.op x x) = (k x y) ∨ (M.op y y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq195007
       have i₂ := eq3836 x y
       grind)
    | exact superpose eq3836 eq195007
    | (have j1 := eq3836 x y
       grind)
    | (have r₁ := eq195007
       have r₂ := eq3836 x y
       grind)
    | exact resolve eq195007 eq3836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3836 eq195007
  have eq199815 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k x y) ∨ (M.op x x) = (k x y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq199808
  have eq199816 : (M.op y y) = (k x y) ∨ (M.op x x) = (k x y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq199815
  have eq199821 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq199803
  have eq199822 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq199821
  have eq199824 : (M.op y y) = (k x y) ∨ (M.op x x) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq199816
       have r₂ := eq12 x y
       grind)
    | exact resolve eq199816 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199816
  have eq205172 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq7977 x y
       have i₂ := eq199824
       grind)
    | exact superpose eq199824 eq7977
    | (have j0 := eq7977 x y
       grind)
    | (have r₁ := eq7977 x y
       have r₂ := eq199824
       grind)
    | exact resolve eq7977 eq199824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7977
  have eq205186 : (M.op x x) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by grind
  have eq205190 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
  clear eq205172
  have eq205204 : (M.op x x) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq205190
       have r₂ := eq205186
       grind)
    | exact resolve eq205190 eq205186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205190
  have eq293271 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X1)
       have i₂ := eq138677 X1 (σ X0)
       grind)
    | exact superpose eq138677 eq38
    | (have j1 := eq138677 X1 (σ X0)
       grind)
    | exact resolve eq38 eq138677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq138677
  have eq293276 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq293271 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq293271
    | (have j0 := eq293271 X0 X1
       grind)
    | exact resolve eq293271 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293271
  have eq293292 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq293276 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq293276
    | (have j0 := eq293276 X0 X1
       grind)
    | exact resolve eq293276 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293276
  have eq293303 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq293292 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq293292
    | (have j0 := eq293292 X0 X1
       grind)
    | exact resolve eq293292 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293292
  have eq293309 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq293303 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq293303
    | (have j0 := eq293303 X0 X1
       grind)
    | exact resolve eq293303 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293303
  have eq293310 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq293309 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq293309
    | (have j0 := eq293309 X0 X1
       grind)
    | exact resolve eq293309 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293309
  have eq308358 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq293310 x y
       grind)
    | exact superpose eq293310 eq16
    | (have j1 := eq293310 x y
       grind)
    | exact resolve eq16 eq293310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293310
  have eq439030 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2843 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2843
    | (have j0 := eq2843 (σ X0) X1
       grind)
    | exact resolve eq2843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2843
  have eq439061 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq439030 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq439030
    | (have j0 := eq439030 X0 X1
       grind)
    | exact resolve eq439030 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439030
  have eq439064 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq439061 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq439061
    | (have j0 := eq439061 X0 X1
       grind)
    | exact resolve eq439061 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq439061
  have eq439067 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq439064 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq439064
    | (have j0 := eq439064 X0 X1
       grind)
    | exact resolve eq439064 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439064
  have eq439072 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq439067 x y
       have i₂ := eq199824
       grind)
    | exact superpose eq199824 eq439067
    | (have j0 := eq439067 x y
       grind)
    | exact resolve eq439067 eq199824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199824 eq439067
  have eq439161 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x x) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq439072
       have r₂ := eq12 x y
       grind)
    | exact resolve eq439072 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439072
  have eq439916 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq439161
       grind)
    | exact superpose eq439161 eq10
    | exact resolve eq10 eq439161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439161
  have eq439952 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq439916
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq439916
    | exact resolve eq439916 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439916
  have eq439953 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x x) = (k x y) := by
    first
    | (have r₁ := eq439952
       have r₂ := eq205186
       grind)
    | exact resolve eq439952 eq205186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205186 eq439952
  have eq439963 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x x) = (k x y) ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq308358
       have i₂ := eq439953
       grind)
    | exact superpose eq439953 eq308358
    | (have r₁ := eq308358
       have r₂ := eq439953
       grind)
    | exact resolve eq308358 eq439953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308358 eq439953
  have eq439986 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x x) = (k x y) := by grind
  clear eq439963
  have eq439987 : (M.op x y) = (k x y) ∨ (M.op x x) = (k x y) := by grind
  clear eq439986
  have eq440030 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by grind
  clear eq439987
  have eq440039 : (M.op x x) = (k x y) := by
    first
    | (have r₁ := eq440030
       have r₂ := eq205204
       grind)
    | exact resolve eq440030 eq205204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205204 eq440030
  have eq440153 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq579 x y
       have i₂ := eq440039
       grind)
    | exact superpose eq440039 eq579
    | (have j0 := eq579 x y
       grind)
    | exact resolve eq579 eq440039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq440154 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq580 x y
       have i₂ := eq440039
       grind)
    | exact superpose eq440039 eq580
    | (have j0 := eq580 x y
       grind)
    | exact resolve eq580 eq440039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq440181 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq440154
  have eq440182 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq440153
  have eq440953 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq440181
       grind)
    | exact superpose eq440181 eq16
    | exact resolve eq16 eq440181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440181
  have eq440969 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq440953
       have i₂ := eq199822
       grind)
    | exact superpose eq199822 eq440953
    | exact resolve eq440953 eq199822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440953
  have eq440975 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq440969
  have eq441012 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq440975
       grind)
    | exact superpose eq440975 eq16
    | exact resolve eq16 eq440975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443716 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9989 x y
       have i₂ := eq440039
       grind)
    | exact superpose eq440039 eq9989
    | (have j0 := eq9989 x y
       grind)
    | exact resolve eq9989 eq440039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9989
  have eq443722 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq443716
  have eq443738 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq440975
       have i₂ := eq443722
       grind)
    | exact superpose eq443722 eq440975
    | exact resolve eq440975 eq443722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440975 eq443722
  have eq443747 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq443738
  have eq443799 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq443747
       have i₂ := eq199822
       grind)
    | exact superpose eq199822 eq443747
    | exact resolve eq443747 eq199822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199822 eq443747
  have eq443857 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq443799
  have eq443876 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq443857
       have r₂ := eq441012
       grind)
    | exact resolve eq443857 eq441012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441012 eq443857
  have eq443928 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq443876
       grind)
    | exact superpose eq443876 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq443876
       grind)
    | exact resolve eq13 eq443876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443939 : (M.op x x) = (M.op y y) ∨ (M.op y y) = (k x y) := by grind
  clear eq443928
  have eq443942 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq443939
       have i₂ := eq440039
       grind)
    | exact superpose eq440039 eq443939
    | exact resolve eq443939 eq440039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440039 eq443939
  have eq443943 : (M.op x x) = (M.op y y) := by grind
  clear eq443942
  have eq443959 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq440182
       have i₂ := eq443943
       grind)
    | exact superpose eq443943 eq440182
    | exact resolve eq440182 eq443943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440182 eq443943
  have eq444102 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq443959
  have eq444184 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq444102
       grind)
    | exact superpose eq444102 eq16
    | exact resolve eq16 eq444102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444102
  have eq444231 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq444184
       have i₂ := eq443876
       grind)
    | exact superpose eq443876 eq444184
    | exact resolve eq444184 eq443876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443876 eq444184
  have eq444232 : False := by grind
  exact eq444232

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq41 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24 x y
       grind)
    | exact superpose eq24 eq16
    | (have j1 := eq24 x y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq24 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq24 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq296 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (τ X0) (τ X1)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq44
    | (have j0 := eq44 (τ X0) (τ X1)
       grind)
    | exact resolve eq44 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq296 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq296
    | (have j0 := eq296 X0 X1
       grind)
    | exact resolve eq296 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq306 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq303
    | (have j0 := eq303 X0 X1
       grind)
    | exact resolve eq303 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq308 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq306
    | (have j0 := eq306 X0 X1
       grind)
    | exact resolve eq306 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq309 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq308
    | (have j0 := eq308 X0 X1
       grind)
    | exact resolve eq308 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq310 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq309 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq309
    | (have j0 := eq309 X0 X1
       grind)
    | exact resolve eq309 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq311 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq310
    | (have j0 := eq310 X0 X1
       grind)
    | exact resolve eq310 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq356 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (τ X0) (τ X1)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq45
    | (have j0 := eq45 (τ X0) (τ X1)
       grind)
    | exact resolve eq45 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq363 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq356 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq356
    | (have j0 := eq356 X0 X1
       grind)
    | exact resolve eq356 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq366 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq363 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq363
    | (have j0 := eq363 X0 X1
       grind)
    | exact resolve eq363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq368 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq366 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq366
    | (have j0 := eq366 X0 X1
       grind)
    | exact resolve eq366 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq369 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq370 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq369 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq369
    | (have j0 := eq369 X0 X1
       grind)
    | exact resolve eq369 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq371 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq370 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq370
    | (have j0 := eq370 X0 X1
       grind)
    | exact resolve eq370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq416 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq41
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq41 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq416
  have eq2220 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq417
       grind)
    | exact superpose eq417 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq417
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq417
       grind)
    | exact resolve eq12 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq2222 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2220
  have eq2223 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2222
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2222
    | exact resolve eq2222 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222
  have eq17893 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq2223
       grind)
    | exact superpose eq2223 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2223
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2223
       grind)
    | exact resolve eq13 eq2223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17894 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq2223
       grind)
    | exact superpose eq2223 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2223
       grind)
    | exact resolve eq12 eq2223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223
  have eq17895 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq17893
  have eq17898 : (σ x) = (σ (k x y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17894
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17894
    | exact resolve eq17894 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17894
  have eq17899 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq17898
  have eq17900 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17895
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17895
    | exact resolve eq17895 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17895
  have eq17902 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17900
       have r₂ := eq17899
       grind)
    | exact resolve eq17900 eq17899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17899 eq17900
  have eq18506 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq17902
       grind)
    | exact superpose eq17902 eq10
    | exact resolve eq10 eq17902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17902
  have eq18655 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18506
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq18506
    | exact resolve eq18506 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18506
  have eq18658 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq371 x y
       grind)
    | (have r₁ := eq18655
       have r₂ := eq371 x y
       grind)
    | exact resolve eq18655 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq18655
  have eq18850 : (k x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq18658
       grind)
    | exact superpose eq18658 eq10
    | exact resolve eq10 eq18658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18658
  have eq19001 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18850
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18850
    | exact resolve eq18850 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18850
  have eq19002 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq311 x y
       grind)
    | (have r₁ := eq19001
       have r₂ := eq311 x y
       grind)
    | exact resolve eq19001 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq19001
  have eq19195 : y ≠ y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19002
       grind)
    | exact superpose eq19002 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq19002
       grind)
    | exact resolve eq12 eq19002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19196 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq19197 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq19195
  have eq19552 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44 x y
       have i₂ := eq19197
       grind)
    | exact superpose eq19197 eq44
    | (have j0 := eq44 x y
       grind)
    | exact resolve eq44 eq19197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq19597 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19552
  have eq25418 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19597
       grind)
    | exact superpose eq19597 eq16
    | exact resolve eq16 eq19597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19597
  have eq26222 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25418
       have i₂ := eq19002
       grind)
    | exact superpose eq19002 eq25418
    | exact resolve eq25418 eq19002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25418
  have eq26225 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq26222
  have eq26226 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26225
       have r₂ := eq19196
       grind)
    | exact resolve eq26225 eq19196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26225
  have eq26572 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26226
       grind)
    | exact superpose eq26226 eq16
    | exact resolve eq16 eq26226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26573 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq26226
       grind)
    | exact superpose eq26226 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq26226
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq26226
       grind)
    | exact resolve eq13 eq26226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26226
  have eq26575 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26573
  have eq26579 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26575
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq26575
    | exact resolve eq26575 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26575
  have eq27035 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26572
       have i₂ := eq19002
       grind)
    | exact superpose eq19002 eq26572
    | exact resolve eq26572 eq19002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19002 eq26572
  have eq27039 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27035
       have r₂ := eq19196
       grind)
    | exact resolve eq27035 eq19196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19196 eq27035
  have eq27957 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26579
       have i₂ := eq19197
       grind)
    | exact superpose eq19197 eq26579
    | exact resolve eq26579 eq19197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19197 eq26579
  have eq28078 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq27957
  have eq28178 : x = (M.op x y) := by
    first
    | (have r₁ := eq28078
       have r₂ := eq27039
       grind)
    | exact resolve eq28078 eq27039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27039 eq28078
  have eq28518 : x ≠ x ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq28178
       grind)
    | exact superpose eq28178 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq28178
       grind)
    | exact resolve eq13 eq28178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28519 : x ≠ y ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq28178
       grind)
    | exact superpose eq28178 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq28178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28520 : y = (k x y) ∨ x = y := by grind
  clear eq28518
  have eq29116 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq45 x y
       have i₂ := eq28520
       grind)
    | exact superpose eq28520 eq45
    | (have j0 := eq45 x y
       grind)
    | exact resolve eq45 eq28520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq29142 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq29116
  have eq31626 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq29142
       grind)
    | exact superpose eq29142 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq29142
       grind)
    | exact resolve eq12 eq29142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29142
  have eq31628 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq31626
  have eq31629 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq31628
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq31628
    | exact resolve eq31628 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31628
  have eq32467 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq31629
       grind)
    | exact superpose eq31629 eq16
    | exact resolve eq16 eq31629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31629
  have eq32476 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq32467
       have i₂ := eq28178
       grind)
    | exact superpose eq28178 eq32467
    | exact resolve eq32467 eq28178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32467
  have eq32477 : (σ x) = (σ (k x y)) ∨ x = y := by grind
  clear eq32476
  have eq32866 : (k x y) = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq32477
       grind)
    | exact superpose eq32477 eq10
    | exact resolve eq10 eq32477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32477
  have eq33034 : x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq32866
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq32866
    | exact resolve eq32866 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32866
  have eq33035 : x = (k x y) := by
    first
    | (have r₁ := eq33034
       have r₂ := eq28519
       grind)
    | exact resolve eq33034 eq28519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28519 eq33034
  have eq33428 : x = y ∨ x = y := by
    first
    | (have i₁ := eq28520
       have i₂ := eq33035
       grind)
    | exact superpose eq33035 eq28520
    | exact resolve eq28520 eq33035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28520
  have eq33459 : x = y := by grind
  clear eq33428
  have eq33856 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33459
       grind)
    | exact superpose eq33459 eq16
    | exact resolve eq16 eq33459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33857 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq41
       have i₂ := eq33459
       grind)
    | exact superpose eq33459 eq41
    | exact resolve eq41 eq33459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq33889 : x = (M.op x x) := by
    first
    | (have i₁ := eq28178
       have i₂ := eq33459
       grind)
    | exact superpose eq33459 eq28178
    | exact resolve eq28178 eq33459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28178
  have eq33891 : x = (k x x) := by
    first
    | (have i₁ := eq33035
       have i₂ := eq33459
       grind)
    | exact superpose eq33459 eq33035
    | exact resolve eq33035 eq33459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33035 eq33459
  have eq33920 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq33857
  have eq33921 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq33920
       have i₂ := eq33891
       grind)
    | exact superpose eq33891 eq33920
    | exact resolve eq33920 eq33891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33891 eq33920
  have eq33922 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq33856
       have i₂ := eq33889
       grind)
    | exact superpose eq33889 eq33856
    | exact resolve eq33856 eq33889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33856
  have eq33923 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq33921
       have i₂ := eq33889
       grind)
    | exact superpose eq33889 eq33921
    | exact resolve eq33921 eq33889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33889 eq33921
  have eq33924 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq33923
  have eq33925 : False := by grind
  exact eq33925

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pxx_pyy_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23 (σ X0)
       grind)
    | exact superpose eq23 eq15
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq23 (τ X0)
       grind)
    | exact superpose eq23 eq17
    | exact resolve eq17 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq25
    | exact resolve eq25 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq27
    | exact resolve eq27 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq27
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq66 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq68 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       have j1 := eq61 X1 X0
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq63 X1 X0
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq63 X0 X0
       have r₂ := eq61 X0 X0
       grind)
    | exact resolve eq63 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq63
  have eq71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq73 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq103 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq68
    | (have j0 := eq68 (σ X0) (σ X1)
       grind)
    | exact resolve eq68 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq68 X1 (τ X0)
       grind)
    | exact superpose eq68 eq18
    | (have j1 := eq68 X1 (τ X0)
       grind)
    | exact resolve eq18 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq68 (τ X1) X0
       grind)
    | exact superpose eq68 eq17
    | (have j1 := eq68 (τ X1) X0
       grind)
    | exact resolve eq17 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq249 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq231 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq231
    | (have j0 := eq231 X0 X1
       grind)
    | exact resolve eq231 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq258 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq210
    | (have j0 := eq210 X0 X1
       grind)
    | exact resolve eq210 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq264 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq249 X0 X1
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq249
    | (have j0 := eq249 X0 X1
       grind)
    | exact resolve eq249 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq268 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq258 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq258
    | (have j0 := eq258 X0 X1
       grind)
    | exact resolve eq258 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq351 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq560 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq71 X1 X0
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq71 X1 X0
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq612 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq560 X0 X1
       have j1 := eq103 X1 (σ X0)
       grind)
    | (have r₁ := eq560 X0 X0
       have r₂ := eq103 X0 (σ X0)
       grind)
    | (have r₁ := eq560 X0 X0
       have r₂ := eq103 X0 (σ X0)
       grind)
    | exact resolve eq560 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq560
  have eq664 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq612 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq612
    | (have j0 := eq612 X0 X1
       grind)
    | exact resolve eq612 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq698 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq664 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq664
    | (have j0 := eq664 X0 X1
       grind)
    | exact resolve eq664 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq718 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq698 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq698
    | (have j0 := eq698 X0 X1
       grind)
    | exact resolve eq698 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq3680 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq234 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq234
    | exact resolve eq234 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq3864 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3680 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3680
    | (have j0 := eq3680 X0 X1
       grind)
    | exact resolve eq3680 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3680
  have eq4137 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1
       have i₂ := eq264 X0 X1
       grind)
    | exact superpose eq264 eq351
    | (have j0 := eq351 X0 X1
       have j1 := eq264 X0 X1
       grind)
    | (have r₁ := eq351 X0 X1
       have r₂ := eq264 X0 X1
       grind)
    | exact resolve eq351 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq351
  have eq4262 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq4137 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4137
  have eq7881 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq718 (τ X1) (τ X0)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq718
    | (have j0 := eq718 (τ X0) (τ X1)
       grind)
    | exact resolve eq718 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq7956 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7881 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7881
    | (have j0 := eq7881 X0 X1
       grind)
    | exact resolve eq7881 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7881
  have eq7981 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7956 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq7956
    | (have j0 := eq7956 X0 X1
       grind)
    | exact resolve eq7956 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7956
  have eq8002 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7981 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7981
    | (have j0 := eq7981 X0 X1
       grind)
    | exact resolve eq7981 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7981
  have eq8013 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8002 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq8002
    | (have j0 := eq8002 X0 X1
       grind)
    | exact resolve eq8002 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8002
  have eq8020 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8013 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8013
    | (have j0 := eq8013 X0 X1
       grind)
    | exact resolve eq8013 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8013
  have eq8023 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8020 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq8020
    | (have j0 := eq8020 X0 X1
       grind)
    | exact resolve eq8020 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8020
  have eq8024 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8023 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq8023
    | (have j0 := eq8023 X0 X1
       grind)
    | exact resolve eq8023 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8023
  have eq9736 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq268 X0 X1
       grind)
    | exact superpose eq268 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq268 X0 X1
       grind)
    | exact resolve eq13 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq9817 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9736 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq9736
    | (have j0 := eq9736 X0 X1
       grind)
    | exact resolve eq9736 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9736
  have eq9932 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9817 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq9817
    | (have j0 := eq9817 X0 X1
       grind)
    | exact resolve eq9817 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9817
  have eq9933 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq9932 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9932
  have eq10014 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9933 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq9933
    | (have j0 := eq9933 X0 X1
       grind)
    | exact resolve eq9933 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9933
  have eq10045 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10014 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10014
    | (have j0 := eq10014 X0 X1
       grind)
    | exact resolve eq10014 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10014
  have eq10046 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10045 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10045
  have eq105012 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq4262 X1 (τ X0)
       grind)
    | exact superpose eq4262 eq17
    | (have j1 := eq4262 X1 (τ X0)
       grind)
    | exact resolve eq17 eq4262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq105051 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq4262 (σ X0) X1
       grind)
    | exact superpose eq4262 eq22
    | (have j1 := eq4262 (σ X0) X1
       grind)
    | exact resolve eq22 eq4262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4262
  have eq105061 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq105051 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq105051
    | (have j0 := eq105051 X0 X1
       grind)
    | exact resolve eq105051 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105051
  have eq105070 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105012 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq105012
    | (have j0 := eq105012 X0 X1
       grind)
    | exact resolve eq105012 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105012
  have eq105092 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq105061 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq105061
    | (have j0 := eq105061 X0 X1
       grind)
    | exact resolve eq105061 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105061
  have eq105097 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105070 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq105070
    | (have j0 := eq105070 X0 X1
       grind)
    | exact resolve eq105070 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105070
  have eq105114 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq105092 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq105092
    | (have j0 := eq105092 X0 X1
       grind)
    | exact resolve eq105092 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105092
  have eq105119 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105097 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq105097
    | (have j0 := eq105097 X0 X1
       grind)
    | exact resolve eq105097 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105097
  have eq105129 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq105114 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105114
    | (have j0 := eq105114 X0 X1
       grind)
    | exact resolve eq105114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105114
  have eq105132 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq105119 X0 X1
       have i₂ := eq73 X1 X0
       grind)
    | exact superpose eq73 eq105119
    | (have j0 := eq105119 X0 X1
       grind)
    | exact resolve eq105119 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq105119
  have eq105136 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq105129 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105129
    | (have j0 := eq105129 X0 X1
       grind)
    | exact resolve eq105129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105129
  have eq107773 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq105136 (σ X0) X1
       grind)
    | exact superpose eq105136 eq22
    | (have j1 := eq105136 (σ X0) X1
       grind)
    | exact resolve eq22 eq105136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105136
  have eq107870 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq107773 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq107773
    | (have j0 := eq107773 X0 X1
       grind)
    | exact resolve eq107773 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107773
  have eq108003 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq107870 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq107870
    | (have j0 := eq107870 X0 X1
       grind)
    | exact resolve eq107870 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107870
  have eq118103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8024 X0 X1
       have i₂ := eq105132 X0 X1
       grind)
    | exact superpose eq105132 eq8024
    | (have j0 := eq8024 X1 X0
       have j1 := eq105132 X1 X0
       grind)
    | (have r₁ := eq8024 X0 X1
       have r₂ := eq105132 X0 X1
       grind)
    | (have r₁ := eq8024 X1 X1
       have r₂ := eq105132 X1 X1
       grind)
    | exact resolve eq8024 eq105132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8024
  have eq118206 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq105132 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105132
  have eq118221 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq118103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118103
  have eq118322 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq118221 X0 X1
       have j1 := eq118206 X1 X0
       grind)
    | (have r₁ := eq118221 X0 X1
       have r₂ := eq118206 X0 X1
       grind)
    | (have r₁ := eq118221 X1 X0
       have r₂ := eq118206 X0 X1
       grind)
    | (have r₁ := eq118221 X0 X0
       have r₂ := eq118206 X0 X0
       grind)
    | exact resolve eq118221 eq118206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118206 eq118221
  have eq136002 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq118322 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq118322
    | (have j0 := eq118322 (σ X0) X1
       grind)
    | exact resolve eq118322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118322
  have eq136058 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq136002 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq136002
    | (have j0 := eq136002 X0 X1
       grind)
    | exact resolve eq136002 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq136002
  have eq182671 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X1)
       have i₂ := eq108003 X1 (σ X0)
       grind)
    | exact superpose eq108003 eq38
    | (have j1 := eq108003 X1 (σ X0)
       grind)
    | exact resolve eq38 eq108003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108003
  have eq182720 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq182671 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq182671
    | (have j0 := eq182671 X0 X1
       grind)
    | exact resolve eq182671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182671
  have eq182745 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq182720 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq182720
    | (have j0 := eq182720 X0 X1
       grind)
    | exact resolve eq182720 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182720
  have eq182762 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq182745 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq182745
    | (have j0 := eq182745 X0 X1
       grind)
    | exact resolve eq182745 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182745
  have eq182775 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq182762 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq182762
    | (have j0 := eq182762 X0 X1
       grind)
    | exact resolve eq182762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182762
  have eq182780 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq182775 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq182775
    | (have j0 := eq182775 X0 X1
       grind)
    | exact resolve eq182775 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182775
  have eq192408 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq182780 y x
       grind)
    | exact superpose eq182780 eq16
    | (have j1 := eq182780 y x
       grind)
    | exact resolve eq16 eq182780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182780
  have eq197206 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq192408
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq192408
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq192408 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197211 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq192408
       have i₂ := eq3864 y x
       grind)
    | exact superpose eq3864 eq192408
    | (have j1 := eq3864 y x
       grind)
    | (have r₁ := eq192408
       have r₂ := eq3864 y x
       grind)
    | exact resolve eq192408 eq3864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3864 eq192408
  have eq197218 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq197211
  have eq197219 : (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq197218
  have eq197224 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq197206
  have eq197225 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq197224
  have eq197227 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq197219
       have r₂ := eq12 y x
       grind)
    | exact resolve eq197219 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197219
  have eq202587 : (M.op y y) ≠ (M.op x x) ∨ (M.op x x) = (k y x) := by grind
  clear eq197227
  have eq283410 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X1)
       have i₂ := eq136058 X1 (σ X0)
       grind)
    | exact superpose eq136058 eq38
    | (have j1 := eq136058 X1 (σ X0)
       grind)
    | exact resolve eq38 eq136058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq136058
  have eq283415 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq283410 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq283410
    | (have j0 := eq283410 X0 X1
       grind)
    | exact resolve eq283410 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283410
  have eq283431 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq283415 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq283415
    | (have j0 := eq283415 X0 X1
       grind)
    | exact resolve eq283415 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283415
  have eq283442 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq283431 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq283431
    | (have j0 := eq283431 X0 X1
       grind)
    | exact resolve eq283431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283431
  have eq283448 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq283442 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq283442
    | (have j0 := eq283442 X0 X1
       grind)
    | exact resolve eq283442 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283442
  have eq283449 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq283448 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq283448
    | (have j0 := eq283448 X0 X1
       grind)
    | exact resolve eq283448 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq283448
  have eq298233 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq283449 y x
       grind)
    | exact superpose eq283449 eq16
    | (have j1 := eq283449 y x
       grind)
    | exact resolve eq16 eq283449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283449
  have eq305788 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq298233
       have i₂ := eq197225
       grind)
    | exact superpose eq197225 eq298233
    | exact resolve eq298233 eq197225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298233
  have eq305791 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq305788
  have eq305792 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq305791
  have eq440486 : ∀ X0 X1 : G, (k (σ X0) X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10046 X1 (τ X0)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10046
    | (have j0 := eq10046 X0 (τ X1)
       grind)
    | exact resolve eq10046 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq440495 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (k (σ X0) X1) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq440486 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq440486
    | (have j0 := eq440486 X0 X1
       grind)
    | exact resolve eq440486 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440486
  have eq440499 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k (σ X0) X1) ≠ (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq440495 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq440495
    | (have j0 := eq440495 X0 X1
       grind)
    | exact resolve eq440495 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440495
  have eq440502 : ∀ X0 X1 : G, (k (σ X0) X1) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq440499 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq440499
    | (have j0 := eq440499 X0 X1
       grind)
    | exact resolve eq440499 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440499
  have eq459824 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq440502 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq440502
    | exact resolve eq440502 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440502
  have eq459832 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq459824 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq459824
    | (have j0 := eq459824 X0 X1
       grind)
    | exact resolve eq459824 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq459824
  have eq459841 : (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq459832 y x
       have i₂ := eq305792
       grind)
    | exact superpose eq305792 eq459832
    | (have j0 := eq459832 y x
       grind)
    | exact resolve eq459832 eq305792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305792 eq459832
  have eq459846 : (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq459841
  have eq459848 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq459846
       have r₂ := eq197225
       grind)
    | exact resolve eq459846 eq197225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197225 eq459846
  have eq459865 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq459848
       grind)
    | exact superpose eq459848 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq459848
       grind)
    | exact resolve eq12 eq459848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459883 : (M.op y y) = (k y x) := by grind
  clear eq459865
  have eq459923 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10046 y x
       have i₂ := eq459883
       grind)
    | exact superpose eq459883 eq10046
    | (have j0 := eq10046 y x
       grind)
    | exact resolve eq10046 eq459883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10046 eq459883
  have eq459971 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq459923
  have eq460385 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq459971
       grind)
    | exact superpose eq459971 eq16
    | exact resolve eq16 eq459971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460401 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq460385
       have i₂ := eq459848
       grind)
    | exact superpose eq459848 eq460385
    | exact resolve eq460385 eq459848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460385
  have eq460402 : (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq460401
  have eq460487 : (M.op y y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq460402
       grind)
    | exact superpose eq460402 eq10
    | exact resolve eq10 eq460402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460402
  have eq460660 : (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq460487
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq460487
    | exact resolve eq460487 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460487
  have eq460665 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq202587
       have i₂ := eq460660
       grind)
    | exact superpose eq460660 eq202587
    | (have r₁ := eq202587
       have r₂ := eq460660
       grind)
    | exact resolve eq202587 eq460660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202587 eq460660
  have eq460969 : (M.op x x) = (k y x) := by grind
  clear eq460665
  have eq461047 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq579 x y
       have i₂ := eq460969
       grind)
    | exact superpose eq460969 eq579
    | (have j0 := eq579 x y
       grind)
    | exact resolve eq579 eq460969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq460969
  have eq461108 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq461047
  have eq461126 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq461108
       have r₂ := eq459971
       grind)
    | exact resolve eq461108 eq459971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459971 eq461108
  have eq461149 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq461126
       grind)
    | exact superpose eq461126 eq16
    | exact resolve eq16 eq461126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461126
  have eq461238 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq461149
       have i₂ := eq459848
       grind)
    | exact superpose eq459848 eq461149
    | exact resolve eq461149 eq459848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459848 eq461149
  have eq461239 : False := by grind
  exact eq461239

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq41 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24 x y
       grind)
    | exact superpose eq24 eq16
    | (have j1 := eq24 x y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq24 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq24 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq296 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (τ X1) (τ X0)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq44
    | (have j0 := eq44 (τ X1) (τ X0)
       grind)
    | exact resolve eq44 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq296 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq296
    | (have j0 := eq296 X0 X1
       grind)
    | exact resolve eq296 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq306 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq303
    | (have j0 := eq303 X0 X1
       grind)
    | exact resolve eq303 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq308 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq306
    | (have j0 := eq306 X0 X1
       grind)
    | exact resolve eq306 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq309 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq308
    | (have j0 := eq308 X0 X1
       grind)
    | exact resolve eq308 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq310 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq309 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq309
    | (have j0 := eq309 X0 X1
       grind)
    | exact resolve eq309 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq311 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq310
    | (have j0 := eq310 X0 X1
       grind)
    | exact resolve eq310 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq356 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (τ X1) (τ X0)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq45
    | (have j0 := eq45 (τ X1) (τ X0)
       grind)
    | exact resolve eq45 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq363 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq356 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq356
    | (have j0 := eq356 X0 X1
       grind)
    | exact resolve eq356 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq366 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq363 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq363
    | (have j0 := eq363 X0 X1
       grind)
    | exact resolve eq363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq368 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq366 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq366
    | (have j0 := eq366 X0 X1
       grind)
    | exact resolve eq366 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq369 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq370 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq369 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq369
    | (have j0 := eq369 X0 X1
       grind)
    | exact resolve eq369 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq371 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq370 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq370
    | (have j0 := eq370 X0 X1
       grind)
    | exact resolve eq370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq416 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq41
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq41 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq417 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq416
  have eq2226 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq417
       grind)
    | exact superpose eq417 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq417
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq417
       grind)
    | exact resolve eq13 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2228 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq417
  have eq2229 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2226
  have eq2230 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2229
       have r₂ := eq2228
       grind)
    | exact resolve eq2229 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228 eq2229
  have eq2232 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2230
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2230
    | exact resolve eq2230 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230
  have eq17920 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2232
       grind)
    | exact superpose eq2232 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2232
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2232
       grind)
    | exact resolve eq12 eq2232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232
  have eq17921 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17920
  have eq17924 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17921
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq17921
    | exact resolve eq17921 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17921
  have eq18351 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq17924
       grind)
    | exact superpose eq17924 eq10
    | exact resolve eq10 eq17924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17924
  have eq18498 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18351
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq18351
    | exact resolve eq18351 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18351
  have eq18501 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq311 y x
       grind)
    | (have r₁ := eq18498
       have r₂ := eq311 y x
       grind)
    | exact resolve eq18498 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq18498
  have eq18697 : (k y x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq18501
       grind)
    | exact superpose eq18501 eq10
    | exact resolve eq10 eq18501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18501
  have eq18846 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18697
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18697
    | exact resolve eq18697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18697
  have eq18847 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq371 y x
       grind)
    | (have r₁ := eq18846
       have r₂ := eq371 y x
       grind)
    | exact resolve eq18846 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq18846
  have eq19034 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18847
       grind)
    | exact superpose eq18847 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18847
       grind)
    | exact resolve eq13 eq18847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19036 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq19037 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq19034
  have eq19038 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19037
       have r₂ := eq19036
       grind)
    | exact resolve eq19037 eq19036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19037
  have eq19425 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45 x y
       have i₂ := eq19038
       grind)
    | exact superpose eq19038 eq45
    | (have j0 := eq45 x y
       grind)
    | exact resolve eq45 eq19038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq19469 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19425
  have eq228924 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19469
       grind)
    | exact superpose eq19469 eq16
    | exact resolve eq16 eq19469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19469
  have eq231752 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq228924
       have i₂ := eq18847
       grind)
    | exact superpose eq18847 eq228924
    | exact resolve eq228924 eq18847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228924
  have eq231755 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq231752
  have eq231756 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq231755
       have r₂ := eq19036
       grind)
    | exact resolve eq231755 eq19036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231755
  have eq233194 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq231756
       grind)
    | exact superpose eq231756 eq16
    | exact resolve eq16 eq231756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233195 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq231756
       grind)
    | exact superpose eq231756 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq231756
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq231756
       grind)
    | exact resolve eq12 eq231756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231756
  have eq233196 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq233195
  have eq233199 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq233196
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq233196
    | exact resolve eq233196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233196
  have eq234641 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq233194
       have i₂ := eq18847
       grind)
    | exact superpose eq18847 eq233194
    | exact resolve eq233194 eq18847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18847 eq233194
  have eq234645 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq234641
       have r₂ := eq19036
       grind)
    | exact resolve eq234641 eq19036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19036 eq234641
  have eq237570 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq233199
       have i₂ := eq19038
       grind)
    | exact superpose eq19038 eq233199
    | exact resolve eq233199 eq19038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19038
  have eq237608 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq233199
       grind)
    | exact superpose eq233199 eq10
    | exact resolve eq10 eq233199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233199
  have eq237740 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq237570
  have eq237797 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq237608
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq237608
    | exact resolve eq237608 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237608
  have eq237824 : x = (M.op x y) := by
    first
    | (have r₁ := eq237740
       have r₂ := eq234645
       grind)
    | exact resolve eq237740 eq234645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234645 eq237740
  have eq237825 : y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq237797
       have r₂ := eq12 y x
       grind)
    | exact resolve eq237797 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237797
  have eq240215 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44 x y
       have i₂ := eq237825
       grind)
    | exact superpose eq237825 eq44
    | (have j0 := eq44 x y
       grind)
    | exact resolve eq44 eq237825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq240254 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq240215
  have eq255424 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq240254
       grind)
    | exact superpose eq240254 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq240254
       grind)
    | exact resolve eq13 eq240254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255426 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq240254
  have eq255427 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq255424
  have eq255428 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq255427
       have r₂ := eq255426
       grind)
    | exact resolve eq255427 eq255426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255427
  have eq255431 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq255428
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq255428
    | exact resolve eq255428 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255428
  have eq255433 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq255431
       have i₂ := eq237825
       grind)
    | exact superpose eq237825 eq255431
    | exact resolve eq255431 eq237825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237825 eq255431
  have eq255434 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq255433
       have r₂ := eq255426
       grind)
    | exact resolve eq255433 eq255426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255426 eq255433
  have eq256620 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq255434
       grind)
    | exact superpose eq255434 eq16
    | exact resolve eq16 eq255434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255434
  have eq256624 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq256620
       have i₂ := eq237824
       grind)
    | exact superpose eq237824 eq256620
    | exact resolve eq256620 eq237824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237824 eq256620
  have eq256625 : False := by grind
  exact eq256625
