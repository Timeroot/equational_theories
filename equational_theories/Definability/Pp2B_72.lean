import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4412`: `x ◇ (x ◇ y) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pyx_pxx_pyx_Equation4412 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4412 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4412.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X1) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
  clear eq18
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
  have eq63 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 x X0 X3
       have i₂ := eq9 x X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq9 X2 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op X2 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X2 X3 (M.op X2 X0)
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X2 (M.op X2 X1) X3
       have i₂ := eq66 X2 X1 X0
       grind)
    | (have i₁ := eq63 X2 (M.op X2 X1) X3
       have i₂ := eq66 X0 X1 X2
       grind)
    | exact superpose eq66 eq63
    | exact resolve eq63 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq113 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X3 X1)
       have i₂ := eq66 X3 X1 X0
       grind)
    | (have i₁ := eq9 X2 X3 (M.op X3 X1)
       have i₂ := eq66 X0 X1 X3
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 X1)) X4) = (M.op (M.op (M.op X2 X3) X2) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq74 X2 X3 X4 (M.op X4 X1)
       have i₂ := eq66 X4 X1 X0
       grind)
    | (have i₁ := eq74 X2 X3 X4 (M.op X4 X1)
       have i₂ := eq66 X0 X1 X4
       grind)
    | exact superpose eq66 eq74
    | exact resolve eq74 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq3119 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq3132 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3141 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X1 X0 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq66
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq66 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq3174 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3186 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3174 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3174
  have eq3187 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3132 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3132
  have eq3188 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3186 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq3186 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq3186 X1 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq3186 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3186
  have eq3218 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3141 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq3141 X0 (M.op X0 X0) X2
       have r₂ := eq12 (M.op X0 X0) (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq3141 X1 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq3141 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3141
  have eq3227 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3187 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq3187 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq3187 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3187
  have eq3238 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X0
       have i₂ := eq3227 X0 X1
       grind)
    | exact superpose eq3227 eq14
    | (have j0 := eq14 X1 X0
       have j1 := eq3227 X0 X1
       grind)
    | exact resolve eq14 eq3227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3247 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X0)
       have i₂ := eq3227 (σ X0) X1
       grind)
    | exact superpose eq3227 eq28
    | (have j1 := eq3227 (σ X0) X1
       grind)
    | exact resolve eq28 eq3227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq3267 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq3227 X0 (τ X1)
       grind)
    | exact superpose eq3227 eq17
    | (have j1 := eq3227 X0 X1
       grind)
    | exact resolve eq17 eq3227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3227
  have eq3274 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3238 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3238
  have eq3289 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3247 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3247
    | (have j0 := eq3247 X0 X1
       grind)
    | exact resolve eq3247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3247
  have eq3541 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3289 X0 (σ X1)
       grind)
    | exact superpose eq3289 eq15
    | (have j1 := eq3289 X0 X1
       grind)
    | exact resolve eq15 eq3289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3289
  have eq3961 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3267 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3267
    | (have j0 := eq3267 X1 X1
       grind)
    | exact resolve eq3267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3267
  have eq4033 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3961 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3961
    | (have j0 := eq3961 X0 X1
       grind)
    | exact resolve eq3961 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3961
  have eq14416 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4033 X1 X0
       have i₂ := eq3541 X0 X1
       grind)
    | exact superpose eq3541 eq4033
    | (have j0 := eq4033 X0 X0
       have j1 := eq3541 X0 X1
       grind)
    | exact resolve eq4033 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3541 eq4033
  have eq14460 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14416 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14416
  have eq17521 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14460 x y
       grind)
    | exact superpose eq14460 eq16
    | (have j1 := eq14460 x x
       grind)
    | (have r₁ := eq16
       have r₂ := eq14460 x y
       grind)
    | exact resolve eq16 eq14460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14460
  have eq17652 : x = (k x x) := by grind
  clear eq17521
  have eq17732 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3274 x x
       have i₂ := eq17652
       grind)
    | exact superpose eq17652 eq3274
    | (have j0 := eq3274 x x
       grind)
    | exact resolve eq3274 eq17652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3274
  have eq17736 : x = (M.op x x) := by grind
  clear eq17732
  have eq17770 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq112 x x X0 X1
       have i₂ := eq17736
       grind)
    | exact superpose eq17736 eq112
    | exact resolve eq112 eq17736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq17772 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq113 x x X0 X1
       have i₂ := eq17736
       grind)
    | exact superpose eq17736 eq113
    | exact resolve eq113 eq17736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq17785 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X1) X0) = (M.op (M.op x x) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201 x x X1 X2 X0
       have i₂ := eq17736
       grind)
    | exact superpose eq17736 eq201
    | exact resolve eq201 eq17736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq17845 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X1) X0) = (M.op x X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17785 X0 X1 X2
       have i₂ := eq17736
       grind)
    | exact superpose eq17736 eq17785
    | exact resolve eq17785 eq17736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17785
  have eq17858 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17772 X0 X1
       have i₂ := eq17736
       grind)
    | exact superpose eq17736 eq17772
    | exact resolve eq17772 eq17736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17772
  have eq17860 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17770 X0 X1
       have i₂ := eq17736
       grind)
    | exact superpose eq17736 eq17770
    | exact resolve eq17770 eq17736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17736 eq17770
  have eq25687 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3188 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3188
  have eq25721 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq25687 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq25687 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq25687 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25687
  have eq41255 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3119 x x
       have i₂ := eq17652
       grind)
    | exact superpose eq17652 eq3119
    | (have j0 := eq3119 x x
       grind)
    | exact resolve eq3119 eq17652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119 eq17652
  have eq41394 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq41255
  have eq41513 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq17845 X0 (σ x) (σ x)
       have i₂ := eq41394
       grind)
    | exact superpose eq41394 eq17845
    | exact resolve eq17845 eq41394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17845
  have eq41565 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq41513 X0
       have i₂ := eq41394
       grind)
    | exact superpose eq41394 eq41513
    | exact resolve eq41513 eq41394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41394 eq41513
  have eq41613 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41565 (σ y)
       grind)
    | exact superpose eq41565 eq16
    | exact resolve eq16 eq41565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41565
  have eq45959 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25721 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25721
  have eq47074 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq45959 (σ X0)
       grind)
    | exact superpose eq45959 eq15
    | exact resolve eq15 eq45959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47076 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq45959 (τ X0)
       grind)
    | exact superpose eq45959 eq31
    | exact resolve eq31 eq45959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47092 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47076 X0
       have i₂ := eq45959 X0
       grind)
    | exact superpose eq45959 eq47076
    | exact resolve eq47076 eq45959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47076
  have eq47094 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47074 X0
       have i₂ := eq45959 X0
       grind)
    | exact superpose eq45959 eq47074
    | exact resolve eq47074 eq45959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45959 eq47074
  have eq48326 : ∀ X0 : G, (M.op x (τ X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq17858 (τ X0) (τ X0)
       have i₂ := eq47092 X0
       grind)
    | exact superpose eq47092 eq17858
    | exact resolve eq17858 eq47092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17858
  have eq48327 : ∀ X0 : G, (M.op x (τ X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17860 (τ X0) (τ X0)
       have i₂ := eq47092 X0
       grind)
    | exact superpose eq47092 eq17860
    | exact resolve eq17860 eq47092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17860
  have eq55711 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3218 (τ X0) (τ X0) x
       have i₂ := eq47092 X0
       grind)
    | exact superpose eq47092 eq3218
    | (have j0 := eq3218 (τ X0) X1 X1
       grind)
    | exact resolve eq3218 eq47092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3218 eq47092
  have eq56543 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op x (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55711 X0 X1
       have i₂ := eq48326 X0
       grind)
    | exact superpose eq48326 eq55711
    | (have j0 := eq55711 X0 X1
       grind)
    | exact resolve eq55711 eq48326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55711
  have eq91643 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (M.op x (τ X0)) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq12 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq48327 X0
       grind)
    | exact superpose eq48327 eq12
    | (have j0 := eq12 (τ (M.op X0 X0)) (τ X0)
       grind)
    | exact resolve eq12 eq48327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48327
  have eq91824 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq91643 X0
       have j1 := eq56543 X0 (τ (M.op X0 X0))
       grind)
    | (have r₁ := eq91643 X0
       have r₂ := eq56543 X0 x
       grind)
    | exact resolve eq91643 eq56543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56543 eq91643
  have eq91895 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq91824 X0
       have i₂ := eq31 X0 (M.op X0 X0)
       grind)
    | exact superpose eq31 eq91824
    | exact resolve eq91824 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq91824
  have eq91914 : ∀ X0 : G, (M.op x (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq91895 X0
       have i₂ := eq48326 X0
       grind)
    | exact superpose eq48326 eq91895
    | exact resolve eq91895 eq48326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48326 eq91895
  have eq92012 : ∀ X0 : G, (M.op x (τ (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq91914 (σ X0)
       grind)
    | exact superpose eq91914 eq22
    | exact resolve eq22 eq91914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq91914
  have eq92050 : ∀ X0 : G, (M.op x (τ (σ X0))) = (k (τ (σ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq92012 X0
       have i₂ := eq47094 X0
       grind)
    | exact superpose eq47094 eq92012
    | exact resolve eq92012 eq47094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92012
  have eq92139 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op x (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq92050 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq92050
    | exact resolve eq92050 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92050
  have eq92208 : ∀ X0 : G, (M.op x X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq92139 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92139
    | exact resolve eq92139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92139
  have eq93060 : ∀ X0 : G, (M.op x (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq92208 (σ X0)
       have i₂ := eq47094 X0
       grind)
    | exact superpose eq47094 eq92208
    | exact resolve eq92208 eq47094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47094
  have eq93124 : ∀ X0 : G, (M.op x (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq93060 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq93060
    | exact resolve eq93060 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93060
  have eq93189 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq93124 X0
       have i₂ := eq92208 X0
       grind)
    | exact superpose eq92208 eq93124
    | exact resolve eq93124 eq92208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92208 eq93124
  have eq93309 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq41613
       have i₂ := eq93189 y
       grind)
    | exact superpose eq93189 eq41613
    | (have r₁ := eq41613
       have r₂ := eq93189 y
       grind)
    | exact resolve eq41613 eq93189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41613 eq93189
  have eq93310 : False := by grind
  exact eq93310

/-- `Equation4417`: `x ◇ (x ◇ y) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pyx_Equation4417 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4417 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4417.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
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
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X2) := by
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
  have eq51 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X3) = (M.op X1 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X1 (M.op X1 x) X3
       have i₂ := eq14 X1 x X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X0)) X3) = (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X1 x X3
       have i₂ := eq14 X1 x X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X2) X3 X1
       have i₂ := eq14 X1 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X2 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91
    | exact resolve eq91 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq97
    | exact resolve eq97 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq207 : (M.op (M.op x y) x) = (M.op y (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq56 (M.op y x)
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | (have i₁ := eq56 x
       have i₂ := eq14 y x X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq57 x
       have i₂ := eq14 sF3 x x
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq350 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op y y)) := by
    first
    | (have i₁ := eq209 (M.op y y)
       have i₂ := eq209 y
       grind)
    | exact superpose eq209 eq209
    | exact resolve eq209 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X3 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 (M.op X1 X2) X3
       have i₂ := eq14 X1 X2 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X2 X1) X2 X3
       have i₂ := eq53 X2 X1 X0
       grind)
    | (have i₁ := eq53 (M.op X2 X1) X2 X3
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op y X0)) X1) = (M.op (M.op (M.op x y) x) y) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y (M.op y X0) X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ y) X0)) X1) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq53
    | exact resolve eq53 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X2 X1)
       have i₂ := eq53 X2 X1 X0
       grind)
    | (have i₁ := eq14 X2 X3 (M.op X2 X1)
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X3) = (M.op (M.op X2 X1) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X2 X3
       have i₂ := eq53 X2 X1 X0
       grind)
    | (have i₁ := eq14 (M.op X2 X1) X2 X3
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq214 eq214
    | exact resolve eq214 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : (M.op (M.op x y) x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op y (σ y))) := by
    first
    | exact superpose eq214 eq209
    | exact resolve eq209 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq58 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 x y X0
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq58
    | (have j0 := eq58 (σ x) X0 (σ y)
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq484 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq422 x
       have i₂ := eq14 x x X0
       grind)
    | exact superpose eq14 eq422
    | (have j1 := eq14 x y X0
       grind)
    | exact resolve eq422 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X3 (M.op (M.op X2 X1) X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 (M.op (M.op X2 X1) X2) X3
       have i₂ := eq51 X2 X1 X0
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq570 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq425 x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq425
    | (have j1 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq425 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (M.op X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y X0 X1
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq816 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 x)) X0) = (M.op (M.op X1 x) (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x y X1 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52
    | (have j0 := eq52 x y X1 X0
       grind)
    | exact resolve eq52 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 y)) X0) = (M.op (M.op X1 y) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y x X1 X0
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq52
    | exact resolve eq52 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq835 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 (M.op (M.op X1 (M.op X1 X3)) X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 X3 (M.op X1 (M.op X1 X3)) X2
       have i₂ := eq53 (M.op X1 (M.op X1 X3)) X1 X0
       grind)
    | (have i₁ := eq52 X1 X3 (M.op X1 (M.op X1 X3)) X2
       have i₂ := eq53 X0 X1 (M.op X1 (M.op X1 X3))
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq942 : ∀ X1 X2 : G, (M.op (M.op (M.op x y) x) (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op X2 y) X2) y) := by
    intro X1 X2
    first
    | (have i₁ := eq54 x y (M.op y x) x
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq946 : ∀ X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op X2 (σ y)) X2) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq57 eq54
    | exact resolve eq54 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq57
  have eq1042 : ∀ X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) := by
    intro X1
    first
    | exact superpose eq214 eq946
    | (have j0 := eq946 X1 (σ x)
       grind)
    | exact resolve eq946 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq1044 : ∀ X1 : G, (M.op (M.op (M.op x y) x) y) = (M.op (M.op (M.op x y) x) (M.op (M.op (M.op x y) x) X1)) := by
    intro X1
    first
    | (have i₁ := eq942 X1 x
       have i₂ := eq209 x
       grind)
    | (have i₁ := eq942 X1 x
       have i₂ := eq209 x
       grind)
    | exact superpose eq209 eq942
    | (have j0 := eq942 X1 x
       grind)
    | exact resolve eq942 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq1084 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op y (σ x))) := by
    first
    | exact superpose eq570 eq209
    | exact resolve eq209 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1129 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1149 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1129 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1151 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1149 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq1149 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq1149 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq6512 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) x)) X0) = (M.op (M.op (M.op X1 (M.op y y)) X1) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq350 eq356
    | exact resolve eq356 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq6517 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) X0) = (M.op (M.op (M.op X1 (M.op y (σ x))) X1) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq1084 eq356
    | exact resolve eq356 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq6522 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op (M.op X1 (M.op y (σ y))) X1) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq413 eq356
    | exact resolve eq356 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq6523 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op (M.op X1 (M.op (σ y) (σ y))) X1) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq402 eq356
    | exact resolve eq356 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq402
  have eq6690 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq364 eq6523
    | exact resolve eq6523 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq6523
  have eq6691 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq6522 X0 x
       have i₂ := eq361 sF3 x
       grind)
    | exact superpose eq361 eq6522
    | exact resolve eq6522 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6522
  have eq6693 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) X0) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq6517 X0 x
       have i₂ := eq361 sF2 x
       grind)
    | exact superpose eq361 eq6517
    | exact resolve eq6517 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6517
  have eq6695 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op x y) x)) X0) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq6512 X0 x
       have i₂ := eq361 y x
       grind)
    | exact superpose eq361 eq6512
    | exact resolve eq6512 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq6512
  have eq6700 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) := by
    intro X0
    first
    | exact superpose eq214 eq6690
    | exact resolve eq6690 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq6690
  have eq6701 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) := by
    intro X0
    first
    | (have i₁ := eq6691 X0
       have i₂ := eq209 (M.op sF0 x)
       grind)
    | exact superpose eq209 eq6691
    | exact resolve eq6691 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6691
  have eq6703 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | (have i₁ := eq6693 X0
       have i₂ := eq209 (M.op sF0 x)
       grind)
    | exact superpose eq209 eq6693
    | exact resolve eq6693 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6693
  have eq6705 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op (M.op x y) x)) X0) := by
    intro X0
    first
    | (have i₁ := eq6695 X0
       have i₂ := eq209 (M.op sF0 x)
       grind)
    | exact superpose eq209 eq6695
    | exact resolve eq6695 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq6695
  have eq6731 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq212 eq6700
    | exact resolve eq6700 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6870 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq6700 eq6701
    | exact resolve eq6701 eq6700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6701
  have eq6871 : (M.op (M.op x y) x) = (M.op (σ y) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq6870 eq212
    | exact resolve eq212 eq6870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq6877 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | exact superpose eq6870 eq6731
    | exact resolve eq6731 eq6870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6731
  have eq6879 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6870 eq570
    | exact resolve eq570 eq6870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq7565 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq207 eq6705
    | exact resolve eq6705 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7758 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq425 eq6703
    | exact resolve eq6703 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425 eq6703
  have eq7869 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq7758
       have i₂ := eq14 sF4 x sF2
       grind)
    | exact superpose eq14 eq7758
    | exact resolve eq7758 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7758
  have eq8162 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op (M.op (M.op X1 (M.op (M.op x y) x)) X1) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq207 eq385
    | exact resolve eq385 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq8388 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq6705 eq8162
    | exact resolve eq8162 eq6705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8162
  have eq8479 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq8388 x
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq8388
    | exact resolve eq8388 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq8388
  have eq8699 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq7869 eq6700
    | exact resolve eq6700 eq7869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6700 eq7869
  have eq8749 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6879 eq8699
    | exact resolve eq8699 eq6879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8699
  have eq8768 : (M.op (M.op x y) x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6870 eq8749
    | exact resolve eq8749 eq6870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8749
  have eq10525 : (M.op (M.op (M.op x y) x) y) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) := by
    first
    | exact superpose eq207 eq816
    | exact resolve eq816 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq816
  have eq10652 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) := by
    first
    | exact superpose eq7565 eq10525
    | exact resolve eq10525 eq7565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7565 eq10525
  have eq11317 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = (M.op (M.op (M.op X0 x) X0) x) := by
    intro X0
    first
    | exact superpose eq10652 eq355
    | exact resolve eq355 eq10652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq11390 : (M.op (M.op x (M.op x y)) x) = (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq11317 x
       have i₂ := eq484 x
       grind)
    | exact superpose eq484 eq11317
    | exact resolve eq11317 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11317
  have eq11402 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq8479 eq11390
    | exact resolve eq11390 eq8479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8479 eq11390
  have eq11406 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq11402
       have i₂ := eq53 x sF0 x
       grind)
    | (have i₁ := eq11402
       have i₂ := eq53 X0 sF0 x
       grind)
    | exact superpose eq53 eq11402
    | exact resolve eq11402 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11422 : (M.op x (M.op x y)) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) := by
    first
    | exact superpose eq11402 eq484
    | exact resolve eq484 eq11402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484 eq11402
  have eq11477 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq10652 eq11422
    | exact resolve eq11422 eq10652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10652 eq11422
  have eq11498 : (M.op x (M.op x y)) = (M.op (σ y) (M.op x (M.op x y))) := by
    first
    | exact superpose eq11477 eq6871
    | exact resolve eq6871 eq11477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6871
  have eq11499 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11477 eq6877
    | exact resolve eq6877 eq11477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11500 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11477 eq6879
    | exact resolve eq6879 eq11477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6879
  have eq11552 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq8768 eq11500
    | exact resolve eq11500 eq8768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8768 eq11500
  have eq11558 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11477 eq11552
    | exact resolve eq11552 eq11477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11552
  have eq11565 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq11477 eq11406
    | exact resolve eq11406 eq11477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11406
  have eq12805 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) = (M.op (M.op x (M.op x y)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) x)) := by
    first
    | (have i₁ := eq1042 x
       have i₂ := eq617 (M.op sF4 sF2) x
       grind)
    | exact superpose eq617 eq1042
    | exact resolve eq1042 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq12806 : (M.op (M.op x (M.op x y)) (M.op (M.op (M.op x y) x) x)) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | exact superpose eq6870 eq12805
    | exact resolve eq12805 eq6870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6870 eq12805
  have eq12807 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) (M.op (M.op (M.op x y) x) x)) := by
    first
    | exact superpose eq6877 eq12806
    | exact resolve eq12806 eq6877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6877 eq12806
  have eq12808 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) x)) := by
    first
    | exact superpose eq11477 eq12807
    | exact resolve eq12807 eq11477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12807
  have eq12809 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq11565 eq12808
    | exact resolve eq12808 eq11565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12808
  have eq12815 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq12809 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq12809
       grind)
    | exact resolve eq13 eq12809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12823 : ∀ X0 : G, (M.op (M.op X0 (M.op x (M.op x y))) X0) = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq12809 eq53
    | exact resolve eq53 eq12809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq12853 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq12815 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12815
  have eq12872 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq12809 eq12823
    | exact resolve eq12823 eq12809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12823
  have eq13165 : (M.op (M.op (M.op x y) x) y) = (M.op (M.op x (M.op x y)) (M.op (M.op (M.op x y) x) x)) := by
    first
    | (have i₁ := eq1044 x
       have i₂ := eq617 (M.op sF0 x) x
       grind)
    | exact superpose eq617 eq1044
    | exact resolve eq1044 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq1044
  have eq13166 : (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) x)) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq11477 eq13165
    | exact resolve eq13165 eq11477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13165
  have eq13167 : (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq11565 eq13166
    | exact resolve eq13166 eq11565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11565 eq13166
  have eq13168 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq12809 eq13167
    | exact resolve eq13167 eq12809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13167
  have eq13522 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq12853 eq1151
    | (have j0 := eq1151 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq1151 eq12853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq13537 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq12809 eq13522
    | (have j0 := eq13522 X0
       grind)
    | exact resolve eq13522 eq12809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13522
  have eq13538 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq13537 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13537
  have eq14746 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X0 y)) X2) (M.op X0 y))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq386 X2 (M.op X0 y) (M.op (M.op X2 (M.op X0 y)) X2) X1
       have i₂ := eq830 (M.op (M.op X2 (M.op X0 y)) X2) X0
       grind)
    | exact superpose eq830 eq386
    | exact resolve eq386 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq15072 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X1 (M.op (M.op (M.op X0 y) (M.op (M.op x y) x)) (M.op X0 y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14746 X0 X1 x
       have i₂ := eq830 x X0
       grind)
    | exact superpose eq830 eq14746
    | exact resolve eq14746 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14746
  have eq15303 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X1 (M.op (M.op x y) x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq6705 eq15072
    | exact resolve eq15072 eq6705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15072
  have eq15434 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq6705 eq15303
    | exact resolve eq15303 eq6705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6705 eq15303
  have eq15504 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 y) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq11477 eq15434
    | exact resolve eq15434 eq11477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15434
  have eq22499 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq13538 eq303
    | exact resolve eq303 eq13538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq22504 : (M.op (σ x) (σ x)) = (σ (k x (M.op x (M.op x y)))) := by
    first
    | exact superpose eq13538 eq36
    | exact resolve eq36 eq13538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq22505 : (M.op (σ y) (σ y)) = (σ (k y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq13538 eq37
    | exact resolve eq37 eq13538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq13538
  have eq22528 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq12853 eq22505
    | exact resolve eq22505 eq12853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22505
  have eq22529 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq12853 eq22504
    | exact resolve eq22504 eq12853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22504
  have eq22574 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq22528
       grind)
    | exact superpose eq22528 eq16
    | exact resolve eq16 eq22528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22528
  have eq22597 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq22529
       grind)
    | exact superpose eq22529 eq16
    | exact resolve eq16 eq22529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34139 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X2 (M.op (M.op X0 y) (M.op (M.op x y) x))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq835 X1 X0 X2 y
       have i₂ := eq830 X0 X0
       grind)
    | exact superpose eq830 eq835
    | exact resolve eq835 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq835
  have eq34666 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X2 (M.op (M.op X0 y) (M.op x (M.op x y)))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq11477 eq34139
    | exact resolve eq34139 eq11477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11477 eq34139
  have eq34840 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X2 (M.op x (M.op x y))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq15504 eq34666
    | exact resolve eq34666 eq15504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15504 eq34666
  have eq34943 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq12872 eq34840
    | exact resolve eq34840 eq12872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12872 eq34840
  have eq35078 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (k X0 (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq34943 X0 X0
       have i₂ := eq12853 X0
       grind)
    | exact superpose eq12853 eq34943
    | exact resolve eq34943 eq12853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35206 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq34943 X0 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq34943
    | exact resolve eq34943 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35289 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1 x x
       have i₂ := eq34943 (M.op (M.op x X1) x) x
       grind)
    | exact superpose eq34943 eq546
    | exact resolve eq546 eq34943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq35509 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X1) := by
    intro X1
    first
    | (have i₁ := eq35289 x X1
       have i₂ := eq34943 X1 x
       grind)
    | exact superpose eq34943 eq35289
    | exact resolve eq35289 eq34943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35289
  have eq40088 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq12853 eq22499
    | exact resolve eq22499 eq12853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12853
  have eq40098 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq22499 eq35078
    | exact resolve eq35078 eq22499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22499 eq35078
  have eq40196 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq40088 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq40088
    | exact resolve eq40088 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41237 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (σ X0) (σ X0))
       have i₂ := eq40196 X0
       grind)
    | exact superpose eq40196 eq15
    | exact resolve eq15 eq40196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40196
  have eq41669 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq34943 (σ X0) (σ X0)
       have i₂ := eq41237 X0
       grind)
    | exact superpose eq41237 eq34943
    | exact resolve eq34943 eq41237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41670 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq35206 (σ X0) (σ X0)
       have i₂ := eq41237 X0
       grind)
    | exact superpose eq41237 eq35206
    | exact resolve eq35206 eq41237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44694 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq35509 eq40098
    | exact resolve eq40098 eq35509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35509 eq40098
  have eq44949 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq44694
       have i₂ := eq40088 (M.op x sF0)
       grind)
    | exact superpose eq40088 eq44694
    | exact resolve eq44694 eq40088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40088 eq44694
  have eq45042 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq12809 eq44949
    | exact resolve eq44949 eq12809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12809 eq44949
  have eq45104 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq45042 eq15
    | exact resolve eq15 eq45042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq75199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq75192
    | exact resolve eq75192 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75192
  have eq75210 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq75199
       have r₂ := eq28
       grind)
    | exact resolve eq75199 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75199
  have eq75215 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq75210 eq22574
    | exact resolve eq22574 eq75210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22574 eq75210
  have eq75360 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq75215
    | exact resolve eq75215 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75215
  have eq75361 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq75360
  have eq75504 : (τ (σ x)) = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq75361 eq22597
    | exact resolve eq22597 eq75361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22597 eq75361
  have eq75638 : x = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq75504
    | exact resolve eq75504 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75504
  have eq75639 : x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq75638
  have eq75720 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41669 y
       have i₂ := eq75639
       grind)
    | exact superpose eq75639 eq41669
    | exact resolve eq41669 eq75639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41669
  have eq75775 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq34943 y y
       have i₂ := eq75639
       grind)
    | exact superpose eq75639 eq34943
    | exact resolve eq34943 eq75639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75639
  have eq75777 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75775
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75775
    | exact resolve eq75775 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75775
  have eq75831 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75720
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq75720
    | exact resolve eq75720 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq75720
  have eq75892 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75831
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq75831
    | exact resolve eq75831 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75831
  have eq75930 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq75892
    | exact resolve eq75892 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75892
  have eq76060 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq75777 eq45104
    | exact resolve eq45104 eq75777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45104
  have eq76165 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq76060
    | exact resolve eq76060 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76060
  have eq76202 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq22529
       have i₂ := eq76165
       grind)
    | exact superpose eq76165 eq22529
    | exact resolve eq22529 eq76165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76210 : (M.op x x) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq422 x
       have i₂ := eq76165
       grind)
    | exact superpose eq76165 eq422
    | exact resolve eq422 eq76165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq76218 : (M.op x (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq41670 x
       have i₂ := eq76165
       grind)
    | exact superpose eq76165 eq41670
    | exact resolve eq41670 eq76165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76319 : (σ (M.op x x)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq76218
       have i₂ := eq41237 x
       grind)
    | exact superpose eq41237 eq76218
    | exact resolve eq76218 eq41237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76218
  have eq76331 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq76202
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq76202
    | exact resolve eq76202 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76202
  have eq76349 : (M.op (σ x) (σ x)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq76319
       have i₂ := eq22529
       grind)
    | exact superpose eq22529 eq76319
    | exact resolve eq76319 eq22529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76319
  have eq77205 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq75930 eq11558
    | exact resolve eq11558 eq75930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11558
  have eq77242 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq75930 eq75777
    | exact resolve eq75777 eq75930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75777 eq75930
  have eq77299 : x = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq77242
  have eq77409 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22529
       have i₂ := eq77299
       grind)
    | exact superpose eq77299 eq22529
    | exact resolve eq22529 eq77299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77425 : (M.op x (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41670 x
       have i₂ := eq77299
       grind)
    | exact superpose eq77299 eq41670
    | exact resolve eq41670 eq77299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41670 eq77299
  have eq77526 : (σ (M.op x x)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77425
       have i₂ := eq41237 x
       grind)
    | exact superpose eq41237 eq77425
    | exact resolve eq77425 eq41237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41237 eq77425
  have eq77538 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77409
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq77409
    | exact resolve eq77409 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77409
  have eq77556 : (M.op (σ x) (σ x)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77526
       have i₂ := eq22529
       grind)
    | exact superpose eq22529 eq77526
    | exact resolve eq77526 eq22529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22529 eq77526
  have eq81544 : (σ x) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq76349 eq76331
    | exact resolve eq76331 eq76349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76331 eq76349
  have eq81614 : (σ x) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq81544
  have eq81755 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq81614 eq11498
    | exact resolve eq11498 eq81614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11498
  have eq81787 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq81614 eq45042
    | exact resolve eq45042 eq81614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81614
  have eq81912 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq81787
    | exact resolve eq81787 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81787
  have eq83326 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq81755 eq34943
    | exact resolve eq34943 eq81755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34943 eq81755
  have eq83328 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq27 eq83326
    | exact resolve eq83326 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83326
  have eq86054 : (M.op (σ x) (σ y)) = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq83328 eq76210
    | exact resolve eq76210 eq83328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76210 eq83328
  have eq86114 : (M.op (σ x) (σ y)) = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq86054
  have eq88494 : x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq76165
       have i₂ := eq86114
       grind)
    | exact superpose eq86114 eq76165
    | exact resolve eq76165 eq86114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76165 eq86114
  have eq88564 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq88494
  have eq94720 : (σ x) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq77556 eq77538
    | exact resolve eq77538 eq77556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77538 eq77556
  have eq94792 : (σ x) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq94720
  have eq94939 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq94792 eq11499
    | exact resolve eq11499 eq94792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11499
  have eq94970 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq94792 eq45042
    | exact resolve eq45042 eq94792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45042 eq94792
  have eq95099 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq94970
    | exact resolve eq94970 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq94970
  have eq95106 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq94939
    | exact resolve eq94939 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq94939
  have eq95162 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq95099 eq28
    | exact resolve eq28 eq95099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95099
  have eq95227 : x = (σ x) := by
    first
    | (have r₁ := eq95162
       have r₂ := eq81912
       grind)
    | exact resolve eq95162 eq81912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81912 eq95162
  have eq95695 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq95227 eq95106
    | exact resolve eq95106 eq95227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95106
  have eq95701 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq95695 eq28
    | exact resolve eq28 eq95695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95695
  have eq95773 : x = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq95701
       have r₂ := eq88564
       grind)
    | exact resolve eq95701 eq88564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88564 eq95701
  have eq95787 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq95773 eq28
    | exact resolve eq28 eq95773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq95816 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq95773 eq77205
    | exact resolve eq77205 eq95773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77205 eq95773
  have eq95841 : x = (M.op x x) := by grind
  clear eq95816
  have eq95963 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq35206 x x
       have i₂ := eq95841
       grind)
    | exact superpose eq95841 eq35206
    | exact resolve eq35206 eq95841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35206
  have eq95965 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq95963
       have i₂ := eq95841
       grind)
    | exact superpose eq95841 eq95963
    | exact resolve eq95963 eq95841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95841 eq95963
  have eq96125 : x = (M.op x y) := by
    first
    | exact superpose eq95965 eq13168
    | exact resolve eq13168 eq95965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13168 eq95965
  have eq96289 : x = (M.op x y) := by
    first
    | (have i₁ := eq96125
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96125
    | exact resolve eq96125 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq96125
  have eq96401 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq96289 eq21
    | exact resolve eq21 eq96289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq96289
  have eq96714 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq96401
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq96401
    | exact resolve eq96401 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq96401
  have eq96825 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq95227 eq96714
    | exact resolve eq96714 eq95227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95227 eq96714
  have eq97006 : False := by grind
  exact eq97006

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyx_pxx_pxy_Equation4419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X1) X0) := by
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
  clear eq44
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X2 X1) X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X1)) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X0 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 (M.op x X1)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
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
  have eq57 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
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
  have eq76 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq72 sF2
       grind)
    | exact superpose eq72 eq50
    | exact resolve eq50 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
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
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq72 sF3
       grind)
    | exact superpose eq72 eq104
    | exact resolve eq104 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq72 y
       grind)
    | exact superpose eq72 eq108
    | exact resolve eq108 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq118 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq122 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq119
       have i₂ := eq72 sF1
       grind)
    | exact superpose eq72 eq119
    | exact resolve eq119 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq124 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq122
       have i₂ := eq72 sF0
       grind)
    | exact superpose eq72 eq122
    | exact resolve eq122 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq146 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq118 eq16
    | exact resolve eq16 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq237 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 y))) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 y) X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq72 (τ X0)
       grind)
    | exact superpose eq72 eq35
    | exact resolve eq35 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq277 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq266 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq266
    | exact resolve eq266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq279 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq277 X0
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq277
    | exact resolve eq277 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq277
  have eq396 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq14
    | exact resolve eq14 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq415 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 y)
       have i₂ := eq237 X0 y
       grind)
    | (have i₁ := eq56 (M.op x y)
       have i₂ := eq237 X0 y
       grind)
    | exact superpose eq237 eq56
    | exact resolve eq56 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq415 X0
       have i₂ := eq237 X0 (M.op sF0 y)
       grind)
    | (have i₁ := eq415 x
       have i₂ := eq237 X0 (M.op sF0 y)
       grind)
    | exact superpose eq237 eq415
    | exact resolve eq415 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq427 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq418 X0
       have i₂ := eq56 sF0
       grind)
    | exact superpose eq56 eq418
    | exact resolve eq418 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq451 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq247 eq56
    | exact resolve eq56 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq247 eq57
    | exact resolve eq57 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq247 eq452
    | exact resolve eq452 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq454 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq247 eq451
    | exact resolve eq451 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq462 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq57 eq453
    | exact resolve eq453 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq463 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq454 X0
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq454
    | exact resolve eq454 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq495 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X2 (M.op X0 y)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 (M.op X0 y) X1 X2
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X1 X2 X3
       have i₂ := eq53 X1 (M.op X1 X2) X3 X0
       grind)
    | (have i₁ := eq55 X1 X2 X3
       have i₂ := eq53 X0 (M.op X1 X2) X3 X1
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq727 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 y X0 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq51
    | exact resolve eq51 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq57 eq51
    | exact resolve eq51 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq823 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq247 eq728
    | (have j0 := eq728 X0 (σ x)
       grind)
    | exact resolve eq728 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq824 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq727 X0 x
       have i₂ := eq237 x X0
       grind)
    | (have i₁ := eq727 x x
       have i₂ := eq237 X0 x
       grind)
    | exact superpose eq237 eq727
    | (have j0 := eq727 X0 x
       grind)
    | exact resolve eq727 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq1187 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X0 X1)
       have i₂ := eq52 X1 y (M.op X0 X1) X0
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1188 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op x X0)
       have i₂ := eq52 X0 sF3 (M.op x X0) x
       grind)
    | exact superpose eq52 eq57
    | exact resolve eq57 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1236 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq247 eq1188
    | exact resolve eq1188 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1237 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1187 X0 X1
       have i₂ := eq237 (M.op X0 X1) (M.op X1 (M.op X1 y))
       grind)
    | exact superpose eq237 eq1187
    | exact resolve eq1187 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1262 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq1236
    | exact resolve eq1236 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1263 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1237 X0 X1
       have i₂ := eq56 X1
       grind)
    | exact superpose eq56 eq1237
    | exact resolve eq1237 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1496 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq146 eq279
    | exact resolve eq279 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq279
  have eq1522 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq247 eq1496
    | exact resolve eq1496 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1524 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq462 eq1522
    | exact resolve eq1522 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522
  have eq1525 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x y) (M.op y y))) := by
    first
    | (have i₁ := eq1524
       have i₂ := eq237 y (M.op y y)
       grind)
    | exact superpose eq237 eq1524
    | exact resolve eq1524 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq1526 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq427 eq1525
    | exact resolve eq1525 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525
  have eq1527 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq124 eq1526
    | exact resolve eq1526 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq2232 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq247 eq823
    | exact resolve eq823 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq2320 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2232 eq51
    | exact resolve eq51 eq2232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232
  have eq2345 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2320 X0
       have i₂ := eq14 sF4 sF3 sF4
       grind)
    | exact superpose eq14 eq2320
    | exact resolve eq2320 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320
  have eq2351 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | (have i₁ := eq2345 x
       have i₂ := eq14 sF4 sF3 x
       grind)
    | exact superpose eq14 eq2345
    | exact resolve eq2345 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345
  have eq2352 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq462 eq2351
    | exact resolve eq2351 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2351
  have eq2353 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1527 eq2352
    | exact resolve eq2352 eq1527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352
  have eq2364 : (M.op (M.op x y) y) = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq824 y
       have i₂ := eq237 sF0 y
       grind)
    | exact superpose eq237 eq824
    | exact resolve eq824 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq2419 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2364 eq51
    | exact resolve eq51 eq2364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2420 : (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq2364 eq13
    | (have r₁ := eq13 (M.op (M.op x y) y) y
       have r₂ := eq2364
       grind)
    | exact resolve eq13 eq2364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2432 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) y) := by grind
  clear eq2420
  have eq2444 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2419 X0
       have i₂ := eq14 sF0 y sF0
       grind)
    | exact superpose eq14 eq2419
    | exact resolve eq2419 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419
  have eq2450 : (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq2444 x
       have i₂ := eq14 sF0 y x
       grind)
    | exact superpose eq14 eq2444
    | exact resolve eq2444 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2444
  have eq2451 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq427 eq2450
    | exact resolve eq2450 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2450
  have eq2541 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq57 eq1262
    | exact resolve eq1262 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1262
  have eq2639 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq462 eq2541
    | exact resolve eq2541 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq2541
  have eq2656 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1527 eq2639
    | exact resolve eq2639 eq1527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527 eq2639
  have eq2664 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq2353 eq2656
    | exact resolve eq2656 eq2353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353 eq2656
  have eq2686 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2664 y
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq2664
    | exact resolve eq2664 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq2664
  have eq3016 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1263 eq240
    | exact resolve eq240 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3124 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq3016 X0
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq3016
    | exact resolve eq3016 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016
  have eq3183 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq2451 eq3124
    | exact resolve eq3124 eq2451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451 eq3124
  have eq3218 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq3183 X0
       have i₂ := eq240 X0 sF0
       grind)
    | exact superpose eq240 eq3183
    | exact resolve eq3183 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq3183
  have eq3232 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq3218 x
       have i₂ := eq14 sF0 x sF0
       grind)
    | exact superpose eq14 eq3218
    | exact resolve eq3218 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3218
  have eq3258 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq463 eq3232
    | exact resolve eq3232 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq3232
  have eq4136 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) (M.op y y))) X0) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq396 (M.op y y) X0
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq396
    | exact resolve eq396 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq396
  have eq4311 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (σ (M.op (M.op y y) (M.op y y))) X0) := by
    intro X0
    first
    | exact superpose eq250 eq4136
    | exact resolve eq4136 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq4136
  have eq4346 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (σ (M.op (M.op x y) (M.op y y))) X0) := by
    intro X0
    first
    | (have i₁ := eq4311 X0
       have i₂ := eq237 y (M.op y y)
       grind)
    | exact superpose eq237 eq4311
    | exact resolve eq4311 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4311
  have eq4362 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (σ (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq427 eq4346
    | exact resolve eq4346 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq4346
  have eq4374 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq124 eq4362
    | exact resolve eq4362 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq4362
  have eq4378 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq247 eq4374
    | exact resolve eq4374 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq4374
  have eq4380 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq2686 eq4378
    | exact resolve eq4378 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686 eq4378
  have eq4382 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq3258 eq4380
    | exact resolve eq4380 eq3258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3258 eq4380
  have eq4685 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq2364 eq495
    | exact resolve eq495 eq2364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2364
  have eq4688 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq1263 eq495
    | exact resolve eq495 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4847 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (M.op x y) (M.op X0 y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq4382 eq4688
    | exact resolve eq4688 eq4382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4688
  have eq4850 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq4685 x
       have i₂ := eq237 sF0 x
       grind)
    | exact superpose eq237 eq4685
    | exact resolve eq4685 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq4685
  have eq4913 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4847 X0 X1
       have i₂ := eq495 X0 X1 sF0
       grind)
    | exact superpose eq495 eq4847
    | exact resolve eq4847 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq4847
  have eq4915 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq4382 eq4850
    | exact resolve eq4850 eq4382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4382 eq4850
  have eq5224 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq4915 eq4913
    | exact resolve eq4913 eq4915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4913 eq4915
  have eq6104 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5224 X1 X2
       have i₂ := eq53 sF0 X1 X2 x
       grind)
    | (have i₁ := eq5224 X1 X2
       have i₂ := eq53 X0 X1 X2 sF0
       grind)
    | exact superpose eq53 eq5224
    | exact resolve eq5224 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq7191 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq1263 eq653
    | exact resolve eq653 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq1263
  have eq7502 : ∀ X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op x y) X2) := by
    intro X1 X2
    first
    | exact superpose eq5224 eq7191
    | exact resolve eq7191 eq5224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5224 eq7191
  have eq23795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23796 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq23795
    | exact resolve eq23795 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23795
  have eq23807 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq23796
       have r₂ := eq28
       grind)
    | exact resolve eq23796 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23796
  have eq23812 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq23807 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq23807
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq23807
       grind)
    | exact resolve eq13 eq23807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23807
  have eq23834 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq23812
  have eq23859 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq23834 eq96
    | exact resolve eq96 eq23834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq23834
  have eq23868 : x = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq23859
  have eq23899 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6104 y x X0
       have i₂ := eq23868
       grind)
    | exact superpose eq23868 eq6104
    | exact resolve eq6104 eq23868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23900 : (M.op y x) = (M.op (M.op x y) y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7502 x y
       have i₂ := eq23868
       grind)
    | exact superpose eq23868 eq7502
    | exact resolve eq7502 eq23868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24467 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23900 eq23899
    | exact resolve eq23899 eq23900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23899 eq23900
  have eq24497 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq24467
  have eq24518 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24497
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24497
    | exact resolve eq24497 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24497
  have eq24541 : x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23868
       have i₂ := eq24518
       grind)
    | exact superpose eq24518 eq23868
    | exact resolve eq23868 eq24518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23868 eq24518
  have eq24561 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq24541
  have eq24578 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24561 eq30
    | exact resolve eq30 eq24561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24561
  have eq24700 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq24578
    | exact resolve eq24578 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24578
  have eq24701 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq24700
  have eq24727 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq24701 eq29
    | exact resolve eq29 eq24701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24701
  have eq24844 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq24727
    | exact resolve eq24727 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq24727
  have eq24845 : x = (M.op x y) ∨ x = y := by grind
  clear eq24844
  have eq24909 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq24845 eq21
    | exact resolve eq21 eq24845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24968 : (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq24845 eq2432
    | exact resolve eq2432 eq24845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2432 eq24845
  have eq25046 : (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq24968
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24968
    | exact resolve eq24968 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24968
  have eq25097 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq24909
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24909
    | exact resolve eq24909 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24909
  have eq25128 : (k x y) = (τ (k (σ (M.op x y)) (σ y))) ∨ x = y := by
    first
    | exact superpose eq25097 eq61
    | exact resolve eq61 eq25097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq25235 : (k x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq173 eq25128
    | exact resolve eq25128 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq25128
  have eq26593 : (M.op x y) = (k x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq25235 eq25046
    | exact resolve eq25046 eq25235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25046 eq25235
  have eq26597 : (M.op x y) = (k x y) ∨ x = y := by grind
  clear eq26593
  have eq27399 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq26597
       grind)
    | exact superpose eq26597 eq45
    | exact resolve eq45 eq26597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq26597
  have eq27429 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq27399
    | exact resolve eq27399 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27399
  have eq27464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27429 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq27429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27429
  have eq27478 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq27464
    | exact resolve eq27464 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27464
  have eq27489 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq27478
       have r₂ := eq28
       grind)
    | exact resolve eq27478 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27478
  have eq29058 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27489 eq6104
    | exact resolve eq6104 eq27489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6104
  have eq29059 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27489 eq7502
    | exact resolve eq7502 eq27489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7502
  have eq120454 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq29058
    | (have j0 := eq29058 (σ y)
       grind)
    | exact resolve eq29058 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29058
  have eq121098 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29059 eq27489
    | exact resolve eq27489 eq29059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27489 eq29059
  have eq121134 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq121098
  have eq121167 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq121134 eq120454
    | exact resolve eq120454 eq121134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120454 eq121134
  have eq121229 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq121167
  have eq121281 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq121229 eq28
    | exact resolve eq28 eq121229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121229
  have eq121569 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq121281
       have r₂ := eq25097
       grind)
    | exact resolve eq121281 eq25097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25097 eq121281
  have eq121579 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq121569 eq30
    | exact resolve eq30 eq121569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq121569
  have eq122046 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq121579
    | exact resolve eq121579 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq121579
  have eq122047 : x = y := by grind
  clear eq122046
  have eq122072 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq122047
       grind)
    | exact superpose eq122047 eq19
    | exact resolve eq19 eq122047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq122073 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq122047
       grind)
    | exact superpose eq122047 eq25
    | exact resolve eq25 eq122047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq122047
  have eq122225 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq122073
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq122073
    | exact resolve eq122073 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq122073
  have eq122258 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq122225 eq27
    | exact resolve eq27 eq122225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq122225
  have eq122735 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq122258 eq77
    | exact resolve eq77 eq122258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq122258
  have eq122861 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq122735
       have i₂ := eq122072
       grind)
    | exact superpose eq122072 eq122735
    | exact resolve eq122735 eq122072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122072 eq122735
  have eq122886 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq122861 eq15
    | exact resolve eq15 eq122861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122861
  have eq122971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq122886
    | exact resolve eq122886 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq122886
  have eq122992 : False := by grind
  exact eq122992

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pxy_Equation4419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X1) X0) := by
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
  clear eq25 eq36
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X2 X1) X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X1)) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X0 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 (M.op x X1)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
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
  have eq57 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq103
    | exact resolve eq103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq114
    | exact resolve eq114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq213 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 y)
       have i₂ := eq213 X0 y
       grind)
    | (have i₁ := eq56 (M.op x y)
       have i₂ := eq213 X0 y
       grind)
    | exact superpose eq213 eq56
    | exact resolve eq56 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq57 (M.op X0 y)
       have i₂ := eq213 X0 sF3
       grind)
    | (have i₁ := eq57 (M.op x y)
       have i₂ := eq213 X0 sF3
       grind)
    | exact superpose eq213 eq57
    | exact resolve eq57 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq373 X0
       have i₂ := eq213 X0 (M.op sF0 sF3)
       grind)
    | (have i₁ := eq373 x
       have i₂ := eq213 X0 (M.op sF0 sF3)
       grind)
    | exact superpose eq213 eq373
    | exact resolve eq373 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq375 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq213 X0 (M.op sF0 y)
       grind)
    | (have i₁ := eq372 x
       have i₂ := eq213 X0 (M.op sF0 y)
       grind)
    | exact superpose eq213 eq372
    | exact resolve eq372 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq385 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq57 eq374
    | exact resolve eq374 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq386 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq375 X0
       have i₂ := eq56 sF0
       grind)
    | exact superpose eq56 eq375
    | exact resolve eq375 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq396 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X2 (M.op X0 y)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 (M.op X0 y) X1 X2
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op X2 (M.op X0 (σ y))) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq53
    | exact resolve eq53 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq222 eq56
    | exact resolve eq56 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq222 eq491
    | exact resolve eq491 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq505 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq494 X0
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq494
    | exact resolve eq494 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq550 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X1 X2 X3
       have i₂ := eq53 X1 (M.op X1 X2) X3 X0
       grind)
    | (have i₁ := eq55 X1 X2 X3
       have i₂ := eq53 X0 (M.op X1 X2) X3 X1
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq650 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq385 sF4
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq385
    | exact resolve eq385 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq696 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 y X0 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq51
    | exact resolve eq51 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq57 eq51
    | exact resolve eq51 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq791 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq222 eq697
    | (have j0 := eq697 X0 (σ x)
       grind)
    | exact resolve eq697 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq792 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq696 X0 x
       have i₂ := eq213 x X0
       grind)
    | (have i₁ := eq696 x x
       have i₂ := eq213 X0 x
       grind)
    | exact superpose eq213 eq696
    | (have j0 := eq696 X0 x
       grind)
    | exact resolve eq696 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq1151 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X0 X1)
       have i₂ := eq52 X1 y (M.op X0 X1) X0
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1202 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1151 X0 X1
       have i₂ := eq213 (M.op X0 X1) (M.op X1 (M.op X1 y))
       grind)
    | exact superpose eq213 eq1151
    | exact resolve eq1151 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1228 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1202 X0 X1
       have i₂ := eq56 X1
       grind)
    | exact superpose eq56 eq1202
    | exact resolve eq1202 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq2075 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq222 eq791
    | exact resolve eq791 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq791
  have eq2195 : (M.op (M.op x y) y) = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq792 y
       have i₂ := eq213 sF0 y
       grind)
    | exact superpose eq213 eq792
    | exact resolve eq792 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2247 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2195 eq51
    | exact resolve eq51 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195
  have eq2272 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2247 X0
       have i₂ := eq14 sF0 y sF0
       grind)
    | exact superpose eq14 eq2247
    | exact resolve eq2247 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247
  have eq2276 : (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq2272 x
       have i₂ := eq14 sF0 y x
       grind)
    | exact superpose eq14 eq2272
    | exact resolve eq2272 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272
  have eq2277 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2276
       have i₂ := eq56 sF0
       grind)
    | exact superpose eq56 eq2276
    | exact resolve eq2276 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276
  have eq2587 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq1228 X0 (M.op X0 y)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq1228
    | exact resolve eq1228 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2704 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq386 eq2587
    | exact resolve eq2587 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq2587
  have eq2723 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq2277 eq2704
    | exact resolve eq2704 eq2277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277 eq2704
  have eq2787 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1228 eq2723
    | exact resolve eq2723 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2788 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq505 eq2723
    | exact resolve eq2723 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505 eq2723
  have eq4066 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (M.op y X1)) y) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq396 (M.op X2 X1) X3 y
       have i₂ := eq51 X2 X1 y X0
       grind)
    | exact superpose eq51 eq396
    | exact resolve eq396 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq4256 : ∀ X1 X2 X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op X2 X1)) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq4066 x X1 X2 X3
       have i₂ := eq213 (M.op x (M.op y X1)) X3
       grind)
    | exact superpose eq213 eq4066
    | exact resolve eq4066 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4066
  have eq4316 : ∀ X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X3
    first
    | exact superpose eq2787 eq4256
    | (have j0 := eq4256 y x X3
       grind)
    | exact resolve eq4256 eq2787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2787 eq4256
  have eq4571 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op X2 (M.op (M.op x y) (σ y))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq397 (M.op X0 y) X1 X2
       have i₂ := eq213 X0 sF3
       grind)
    | (have i₁ := eq397 (M.op x y) X1 X2
       have i₂ := eq213 X0 sF3
       grind)
    | exact superpose eq213 eq397
    | exact resolve eq397 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4797 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq397 eq4571
    | exact resolve eq4571 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq4571
  have eq4856 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq650 eq4797
    | exact resolve eq4797 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq4797
  have eq4904 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq2788 eq4856
    | exact resolve eq4856 eq2788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2788 eq4856
  have eq4942 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq4316 eq4904
    | exact resolve eq4904 eq4316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4316 eq4904
  have eq4966 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4942 X0 X1
       have i₂ := eq396 X0 X1 sF4
       grind)
    | exact superpose eq396 eq4942
    | exact resolve eq4942 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq4942
  have eq5790 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4966 X1 X2
       have i₂ := eq53 sF0 X1 X2 x
       grind)
    | (have i₁ := eq4966 X1 X2
       have i₂ := eq53 X0 X1 X2 sF0
       grind)
    | exact superpose eq53 eq4966
    | exact resolve eq4966 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6943 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq1228 eq550
    | exact resolve eq550 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq1228
  have eq7258 : ∀ X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op x y) X2) := by
    intro X1 X2
    first
    | exact superpose eq4966 eq6943
    | exact resolve eq6943 eq4966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4966 eq6943
  have eq34821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34830 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq34821
    | exact resolve eq34821 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34821
  have eq34841 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq34830
       have r₂ := eq28
       grind)
    | exact resolve eq34830 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34830
  have eq34852 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  have eq34870 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq34841 eq5790
    | exact resolve eq5790 eq34841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34871 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq34841 eq7258
    | exact resolve eq7258 eq34841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34841
  have eq34918 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq34852 eq116
    | exact resolve eq116 eq34852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34852
  have eq34935 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq34918
  have eq34956 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq34935 eq5790
    | exact resolve eq5790 eq34935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34957 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq34935 eq7258
    | exact resolve eq7258 eq34935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34962 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  have eq35044 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq34870
    | (have j0 := eq34870 (σ y)
       grind)
    | exact resolve eq34870 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34870
  have eq35398 : (σ x) ≠ (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  have eq35427 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq35044 eq35398
    | exact resolve eq35398 eq35044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35428 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq35427
  have eq35489 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq34956
    | (have j0 := eq34956 (σ y)
       grind)
    | exact resolve eq34956 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34956
  have eq35822 : (σ x) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq34935 eq34957
    | exact resolve eq34957 eq34935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34935 eq34957
  have eq35851 : (σ x) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq35822
  have eq35867 : (σ x) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq35851
       have r₂ := eq34962
       grind)
    | exact resolve eq35851 eq34962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34962 eq35851
  have eq35883 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq35867 eq35489
    | exact resolve eq35489 eq35867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35489 eq35867
  have eq35934 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35883
  have eq35986 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq34871 eq35934
    | exact resolve eq35934 eq34871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35988 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35934 eq34871
    | exact resolve eq34871 eq35934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34871
  have eq36013 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35988
  have eq36015 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq35986
  have eq36032 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ y)) := by
    first
    | (have r₁ := eq36015
       have r₂ := eq35428
       grind)
    | exact resolve eq36015 eq35428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36015
  have eq36431 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq36032 eq7258
    | exact resolve eq7258 eq36032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36032
  have eq36468 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36013 eq35044
    | exact resolve eq35044 eq36013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35044 eq36013
  have eq36522 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq36468
  have eq36550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq36522
       have r₂ := eq35428
       grind)
    | exact resolve eq36522 eq35428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36522
  have eq36564 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq36550
       have r₂ := eq28
       grind)
    | exact resolve eq36550 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36550
  have eq43888 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq36431 eq35934
    | exact resolve eq35934 eq36431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35934 eq36431
  have eq43924 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43888
  have eq43966 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43924 eq35398
    | exact resolve eq35398 eq43924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35398 eq43924
  have eq44030 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43966
  have eq44063 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq44030
       have r₂ := eq36564
       grind)
    | exact resolve eq44030 eq36564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36564 eq44030
  have eq44078 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq44063
       have r₂ := eq35428
       grind)
    | exact resolve eq44063 eq35428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35428 eq44063
  have eq44101 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq44078 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq44078
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq44078
       grind)
    | exact resolve eq12 eq44078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44119 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq44078 eq7258
    | exact resolve eq7258 eq44078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44126 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq44101
  have eq46052 : (σ x) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq44119 eq44078
    | exact resolve eq44078 eq44119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44078 eq44119
  have eq46080 : (σ x) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq46052
  have eq46137 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq46080 eq792
    | exact resolve eq792 eq46080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46080
  have eq46232 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq46137
    | exact resolve eq46137 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46137
  have eq64641 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq44126 eq61
    | exact resolve eq61 eq44126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44126
  have eq64735 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq64641
    | exact resolve eq64641 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64641
  have eq64738 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq64735
       have r₂ := eq12 x y
       grind)
    | exact resolve eq64735 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64735
  have eq64749 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq64738
  have eq64826 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq64749 eq116
    | exact resolve eq116 eq64749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64749
  have eq64875 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (k x y) := by grind
  clear eq64826
  have eq64879 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq64875
       have r₂ := eq12 x y
       grind)
    | exact resolve eq64875 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64875
  have eq64903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq64879 eq46232
    | exact resolve eq46232 eq64879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46232 eq64879
  have eq64933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (k x y) := by grind
  clear eq64903
  have eq64972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq64933
       have r₂ := eq12 x y
       grind)
    | exact resolve eq64933 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64933
  have eq64994 : x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq64972
       have r₂ := eq28
       grind)
    | exact resolve eq64972 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64972
  have eq65013 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq64994
       grind)
    | exact superpose eq64994 eq45
    | exact resolve eq45 eq64994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64994
  have eq65089 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq65013
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq65013
    | exact resolve eq65013 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65013
  have eq65143 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq65089 eq116
    | exact resolve eq116 eq65089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq65183 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq65089 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq65089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65195 : x = (M.op y y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq65143
  have eq65200 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq65183
    | exact resolve eq65183 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65183
  have eq65387 : (k x y) = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq65195
  have eq89233 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq65200
  have eq380099 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq89233 eq65089
    | exact resolve eq65089 eq89233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65089 eq89233
  have eq380417 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq380099
  have eq380540 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq380417 eq5790
    | exact resolve eq5790 eq380417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380541 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq380417 eq7258
    | exact resolve eq7258 eq380417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380750 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq380540
    | (have j0 := eq380540 (σ y)
       grind)
    | exact resolve eq380540 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380540
  have eq381383 : (σ x) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq380541 eq380417
    | exact resolve eq380417 eq380541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380417 eq380541
  have eq381433 : (σ x) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq381383
  have eq381505 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq381433 eq380750
    | exact resolve eq380750 eq381433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380750 eq381433
  have eq381609 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq381505
  have eq381684 : (M.op y x) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq381609
       grind)
    | exact superpose eq381609 eq56
    | exact resolve eq56 eq381609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq381685 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq213 y X0
       have i₂ := eq381609
       grind)
    | exact superpose eq381609 eq213
    | exact resolve eq213 eq381609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq381698 : (k x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq381609
  have eq382119 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq381685 eq381684
    | exact resolve eq381684 eq381685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381684 eq381685
  have eq382407 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq382119
  have eq382482 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq382407
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq382407
    | exact resolve eq382407 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382407
  have eq383504 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq381698
       grind)
    | exact superpose eq381698 eq45
    | exact resolve eq45 eq381698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq381698
  have eq390275 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq383504
       have i₂ := eq382482
       grind)
    | exact superpose eq382482 eq383504
    | exact resolve eq383504 eq382482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382482 eq383504
  have eq390403 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq390275
  have eq390409 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq390403
    | exact resolve eq390403 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390403
  have eq390572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq390409 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq390409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq390572
    | exact resolve eq390572 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390572
  have eq390600 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq390589
       have r₂ := eq28
       grind)
    | exact resolve eq390589 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390589
  have eq407613 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq407631 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq390600 eq5790
    | exact resolve eq5790 eq390600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407632 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq390600 eq7258
    | exact resolve eq7258 eq390600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390600
  have eq460056 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq407613 eq390409
    | exact resolve eq390409 eq407613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390409 eq407613
  have eq460126 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq460056
  have eq460235 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq460126 eq5790
    | exact resolve eq5790 eq460126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460236 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq460126 eq7258
    | exact resolve eq7258 eq460126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460271 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  have eq461151 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq407631
    | (have j0 := eq407631 (σ y)
       grind)
    | exact resolve eq407631 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407631
  have eq463130 : (σ x) ≠ (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq469965 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq460235
    | (have j0 := eq460235 (σ y)
       grind)
    | exact resolve eq460235 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460235
  have eq472814 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq460126 eq460236
    | exact resolve eq460236 eq460126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460126 eq460236
  have eq472897 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq472814
  have eq472916 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq472897
       have r₂ := eq460271
       grind)
    | exact resolve eq472897 eq460271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460271 eq472897
  have eq474270 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq472916 eq469965
    | exact resolve eq469965 eq472916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469965 eq472916
  have eq474402 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq474270
  have eq474524 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq407632 eq474402
    | exact resolve eq474402 eq407632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474539 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq474402 eq407632
    | exact resolve eq407632 eq474402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407632
  have eq474604 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq474539
  have eq474612 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ y)) := by grind
  clear eq474524
  have eq478899 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq474604 eq461151
    | exact resolve eq461151 eq474604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461151 eq474604
  have eq479054 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq478899
  have eq479111 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq479054
       have r₂ := eq28
       grind)
    | exact resolve eq479054 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479054
  have eq479989 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq479111 eq474402
    | exact resolve eq474402 eq479111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479111
  have eq480058 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq479989
  have eq480116 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq480058 eq2075
    | exact resolve eq2075 eq480058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480288 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq480116
    | exact resolve eq480116 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480116
  have eq480291 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq480058 eq480288
    | exact resolve eq480288 eq480058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480058 eq480288
  have eq480380 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq480291
  have eq530406 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq474612 eq7258
    | exact resolve eq7258 eq474612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474612
  have eq585127 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq530406 eq474402
    | exact resolve eq474402 eq530406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474402 eq530406
  have eq585202 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq585127
  have eq585282 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq585202 eq463130
    | exact resolve eq463130 eq585202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463130
  have eq585439 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq585282
  have eq585492 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq585439
       have r₂ := eq480380
       grind)
    | exact resolve eq585439 eq480380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480380 eq585439
  have eq585848 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq585492 eq5790
    | exact resolve eq5790 eq585492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5790 eq585492
  have eq586374 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq585848
    | (have j0 := eq585848 (σ y)
       grind)
    | exact resolve eq585848 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585848
  have eq586878 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq586374 eq585202
    | exact resolve eq585202 eq586374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585202 eq586374
  have eq587022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq586878
  have eq587066 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq587022
       have r₂ := eq28
       grind)
    | exact resolve eq587022 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587022
  have eq587088 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq587066 eq28
    | exact resolve eq28 eq587066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq587097 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq587066 eq2075
    | exact resolve eq2075 eq587066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075
  have eq587212 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq587097
    | exact resolve eq587097 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq587097
  have eq587215 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq587066 eq587212
    | exact resolve eq587212 eq587066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587066 eq587212
  have eq587250 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq587215 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq587215
       grind)
    | exact resolve eq12 eq587215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587305 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq587250
  have eq588617 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq587305 eq61
    | exact resolve eq61 eq587305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587305
  have eq588833 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq588617
    | exact resolve eq588617 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588617
  have eq588850 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by grind
  clear eq588833
  have eq588931 : (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq587215 eq588850
    | exact resolve eq588850 eq587215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587215 eq588850
  have eq588979 : (τ (σ x)) = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq588931 eq61
    | exact resolve eq61 eq588931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq588931
  have eq589210 : x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq588979
    | exact resolve eq588979 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq588979
  have eq589211 : x = (k x y) := by grind
  clear eq589210
  have eq589284 : x = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq65387
       have i₂ := eq589211
       grind)
    | exact superpose eq589211 eq65387
    | exact resolve eq65387 eq589211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65387 eq589211
  have eq589440 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq589284
  have eq589499 : x = (M.op y x) := by
    first
    | (have r₁ := eq589440
       have r₂ := eq587088
       grind)
    | exact resolve eq589440 eq587088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589440
  have eq590911 : (M.op y x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq7258 x y
       have i₂ := eq589499
       grind)
    | exact superpose eq589499 eq7258
    | exact resolve eq7258 eq589499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7258
  have eq590939 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq590911
       have i₂ := eq589499
       grind)
    | exact superpose eq589499 eq590911
    | exact resolve eq590911 eq589499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590911
  have eq592350 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq590939 eq792
    | exact resolve eq792 eq590939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq590939
  have eq592523 : x = (M.op x y) := by
    first
    | (have i₁ := eq592350
       have i₂ := eq589499
       grind)
    | exact superpose eq589499 eq592350
    | exact resolve eq592350 eq589499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589499 eq592350
  have eq592543 : x = (M.op x y) := by
    first
    | (have i₁ := eq592523
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq592523
    | exact resolve eq592523 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq592523
  have eq593701 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq592543 eq21
    | exact resolve eq21 eq592543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq592543
  have eq594510 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq593701
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq593701
    | exact resolve eq593701 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq593701
  have eq594549 : False := by grind
  exact eq594549

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation4419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq45 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq45 (σ X0)
       grind)
    | exact superpose eq45 eq15
    | exact resolve eq15 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq59
    | exact resolve eq59 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq59
  have eq82 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq82 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq82
    | (have j0 := eq82 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq82 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq16
    | (have j1 := eq83 x y
       grind)
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq737 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq359
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq359
    | (have j1 := eq82 (σ x) (σ y)
       grind)
    | (have r₁ := eq359
       have r₂ := eq82 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq359
       have r₂ := eq82 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq359 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq359
  have eq740 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq737
  have eq741 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq740
       grind)
    | exact superpose eq740 eq16
    | exact resolve eq16 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq742 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq741
       have r₂ := eq68 x
       grind)
    | exact resolve eq741 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq778 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq742
       grind)
    | exact superpose eq742 eq10
    | exact resolve eq10 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq795 : x = y := by
    first
    | (have i₁ := eq778
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq778
    | exact resolve eq778 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq839 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq795
       grind)
    | exact superpose eq795 eq16
    | exact resolve eq16 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq840 : False := by grind
  exact eq840

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation4419 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pxy_pxx_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq50 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq87 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
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
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq104 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq104
    | (have j0 := eq104 X0
       grind)
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq104
  have eq115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq114
    | (have j0 := eq114 X0
       grind)
    | exact resolve eq114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq115 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq115 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq115 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq116 (σ X0)
       grind)
    | exact superpose eq116 eq15
    | exact resolve eq15 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq119
    | exact resolve eq119 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq119
  have eq314 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq16
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1117 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87
    | exact resolve eq87 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq1171 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1117 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1117
    | (have j0 := eq1117 X0 X1
       grind)
    | exact resolve eq1117 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq2095 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq314
       have i₂ := eq1171 x y
       grind)
    | exact superpose eq1171 eq314
    | (have j1 := eq1171 (σ x) (σ y)
       grind)
    | (have r₁ := eq314
       have r₂ := eq1171 x y
       grind)
    | (have r₁ := eq314
       have r₂ := eq1171 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq314
       have r₂ := eq1171 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq314 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq2096 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2095
  have eq84860 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2096
       grind)
    | exact superpose eq2096 eq16
    | exact resolve eq16 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096
  have eq84861 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq84860
       have r₂ := eq130 x
       grind)
    | exact resolve eq84860 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84860
  have eq85680 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq84861
       grind)
    | exact superpose eq84861 eq10
    | exact resolve eq10 eq84861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84861
  have eq85799 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq85680
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq85680
    | exact resolve eq85680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85680
  have eq85805 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85799
       grind)
    | exact superpose eq85799 eq16
    | exact resolve eq16 eq85799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85799
  have eq85806 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq85805
       have r₂ := eq130 x
       grind)
    | exact resolve eq85805 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85805
  have eq86628 : y ≠ y ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq85806
       grind)
    | exact superpose eq85806 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq85806
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq85806
       grind)
    | exact resolve eq12 eq85806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85806
  have eq86751 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq86628
  have eq113854 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq325 x y
       have i₂ := eq86751
       grind)
    | exact superpose eq86751 eq325
    | (have j0 := eq325 x y
       grind)
    | exact resolve eq325 eq86751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq86751
  have eq113881 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq113854
  have eq113882 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq113881
  have eq113905 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq113882
       grind)
    | exact superpose eq113882 eq10
    | exact resolve eq10 eq113882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113882
  have eq114067 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq113905
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq113905
    | exact resolve eq113905 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113905
  have eq114903 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114067
       grind)
    | exact superpose eq114067 eq16
    | exact resolve eq16 eq114067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114067
  have eq114946 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq114903
       have r₂ := eq130 x
       grind)
    | exact resolve eq114903 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114903
  have eq114953 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114946
       grind)
    | exact superpose eq114946 eq16
    | exact resolve eq16 eq114946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114980 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq114946
       grind)
    | exact superpose eq114946 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq114946
       grind)
    | exact resolve eq12 eq114946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114946
  have eq115125 : (σ y) = (k (σ x) (σ y)) := by grind
  clear eq114980
  have eq115199 : (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq115125
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq115125
    | exact resolve eq115125 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115125
  have eq116086 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1171 x y
       have i₂ := eq115199
       grind)
    | exact superpose eq115199 eq1171
    | (have j0 := eq1171 x y
       grind)
    | exact resolve eq1171 eq115199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171 eq115199
  have eq116220 : x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq116086
       have r₂ := eq114953
       grind)
    | exact resolve eq116086 eq114953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116086
  have eq116815 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq116220
       grind)
    | exact superpose eq116220 eq16
    | exact resolve eq16 eq116220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116220
  have eq116865 : y = (M.op x y) := by
    first
    | (have r₁ := eq116815
       have r₂ := eq130 x
       grind)
    | exact resolve eq116815 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq116815
  have eq118213 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq114953
       have i₂ := eq116865
       grind)
    | exact superpose eq116865 eq114953
    | exact resolve eq114953 eq116865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114953 eq116865
  have eq118376 : False := by grind
  exact eq118376

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq36 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq50 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq53 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50
    | (have j0 := eq50 X0
       grind)
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq78 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq85 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq88 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) (σ X0)
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq22
    | (have j1 := eq48 X0
       grind)
    | exact resolve eq22 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq48 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq48 X0
       grind)
    | exact resolve eq12 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq48 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq121 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq119 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq119 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq119 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq251 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq16
    | (have j1 := eq83 x y
       grind)
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq265 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq120 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq120
    | (have j0 := eq120 (τ X0)
       grind)
    | exact resolve eq120 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq266 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq265 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq265
    | (have j0 := eq265 X0
       grind)
    | exact resolve eq265 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq269 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq266 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq266
    | (have j0 := eq266 X0
       grind)
    | exact resolve eq266 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq437 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq462 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq437 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq437
    | (have j0 := eq437 X0
       grind)
    | exact resolve eq437 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq483 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (τ (k (σ (M.op X0 X0)) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36 (k X0 X0) X1
       have i₂ := eq462 X0
       grind)
    | exact superpose eq462 eq36
    | (have j1 := eq462 X0
       grind)
    | exact resolve eq36 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq493 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (k (M.op X0 X0) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq483 X0 X1
       have i₂ := eq36 (M.op X0 X0) X1
       grind)
    | exact superpose eq36 eq483
    | (have j0 := eq483 X0 X1
       grind)
    | exact resolve eq483 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq483
  have eq559 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq597 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq559
    | (have j0 := eq559 X0 X1
       grind)
    | exact resolve eq559 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq652 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq116 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq116
    | exact resolve eq116 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq673 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq652 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq652
    | (have j0 := eq652 X0
       grind)
    | exact resolve eq652 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq677 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq673 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq673
    | (have j0 := eq673 X0
       grind)
    | exact resolve eq673 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq734 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq88 (k (τ X0) (τ X0)) X0
       have i₂ := eq677 (τ X0)
       grind)
    | exact superpose eq677 eq88
    | (have j0 := eq88 (k (τ X0) (τ X0)) X0
       have j1 := eq677 (τ X0)
       grind)
    | exact resolve eq88 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq677
  have eq760 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq734 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq768 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq760 X0
       have j1 := eq269 (τ X0)
       grind)
    | (have r₁ := eq760 X0
       have r₂ := eq269 (τ X0)
       grind)
    | exact resolve eq760 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq760
  have eq772 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq768 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq768
    | (have j0 := eq768 X0
       grind)
    | exact resolve eq768 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq768
  have eq773 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq772 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq772
    | (have j0 := eq772 X0
       grind)
    | exact resolve eq772 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq824 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq773 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq773
    | (have j0 := eq773 (σ X0)
       grind)
    | exact resolve eq773 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq859 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq824 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq824
    | (have j0 := eq824 X0
       grind)
    | exact resolve eq824 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq874 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq859 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq859
    | (have j0 := eq859 X0
       grind)
    | exact resolve eq859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq1005 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq251
       have i₂ := eq597 x y
       grind)
    | exact superpose eq597 eq251
    | (have j1 := eq597 (σ x) (σ y)
       grind)
    | (have r₁ := eq251
       have r₂ := eq597 x y
       grind)
    | (have r₁ := eq251
       have r₂ := eq597 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq251
       have r₂ := eq597 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq251 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq597
  have eq1006 : x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq1005
  have eq1011 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq874 X0
       grind)
    | exact superpose eq874 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq874 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq874 X0
       grind)
    | exact resolve eq12 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq1027 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1011 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq2372 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq78 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2454 : ∀ X0 X1 : G, (k (k X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq493
    | (have j0 := eq493 X1 X1
       grind)
    | exact resolve eq493 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq4453 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = (k (k X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (k X0 X0) X0)
       have i₂ := eq1027 X0 X1
       grind)
    | exact superpose eq1027 eq10
    | (have j1 := eq1027 X0 X1
       grind)
    | exact resolve eq10 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq4500 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4453 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq4453
    | (have j0 := eq4453 X0 X1
       grind)
    | exact resolve eq4453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4453
  have eq4747 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq4755 : ∀ X0 X1 : G, (k X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4500 X0 X1
       have i₂ := eq2454 X0 X0
       grind)
    | exact superpose eq2454 eq4500
    | (have j0 := eq4500 X0 X1
       have j1 := eq2454 X0 X0
       grind)
    | exact resolve eq4500 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454 eq4500
  have eq4810 : ∀ X0 X1 : G, (k X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq4755 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq4755 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq4755 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4755
  have eq4815 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq4747 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq4747 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq4747 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4747
  have eq5039 : ∀ X0 : G, (k X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq4810 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4810
  have eq5043 : ∀ X0 : G, (M.op X0 X0) ≠ (k X0 X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq5039 X0
       have i₂ := eq22 X0 X0
       grind)
    | exact superpose eq22 eq5039
    | (have j0 := eq5039 X0
       grind)
    | exact resolve eq5039 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5039
  have eq5062 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) ≠ (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5043 X0
       have i₂ := eq22 X0 X0
       grind)
    | exact superpose eq22 eq5043
    | (have j0 := eq5043 X0
       grind)
    | exact resolve eq5043 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5043
  have eq5077 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq5062 X0
       have j1 := eq4815 X0 x
       grind)
    | (have r₁ := eq5062 X0
       have r₂ := eq4815 X0 X0
       grind)
    | exact resolve eq5062 eq4815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4815 eq5062
  have eq5096 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5077 (τ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq5077
    | (have j1 := eq78 X0
       grind)
    | exact resolve eq5077 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq5077
  have eq5134 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5096 X0
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq5096
    | (have j0 := eq5096 X0
       grind)
    | exact resolve eq5096 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq5096
  have eq5145 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq5134 X0
       have j1 := eq2372 X0
       grind)
    | (have r₁ := eq5134 X0
       have r₂ := eq2372 X0
       grind)
    | exact resolve eq5134 eq2372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2372 eq5134
  have eq5211 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5145 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5145
    | exact resolve eq5145 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5145
  have eq5297 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq5211 X0
       have i₂ := eq30 (σ X0) X0
       grind)
    | exact superpose eq30 eq5211
    | exact resolve eq5211 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq5211
  have eq5312 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5297 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5297
    | exact resolve eq5297 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5297
  have eq5332 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0 X1
       have i₂ := eq5312 X0
       grind)
    | exact superpose eq5312 eq121
    | (have j0 := eq121 X0 X1
       grind)
    | exact resolve eq121 eq5312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq5362 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq5312 (σ X0)
       grind)
    | exact superpose eq5312 eq15
    | exact resolve eq15 eq5312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5390 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5362 X0
       have i₂ := eq5312 X0
       grind)
    | exact superpose eq5312 eq5362
    | exact resolve eq5362 eq5312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5312 eq5362
  have eq101134 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1006
       grind)
    | exact superpose eq1006 eq16
    | exact resolve eq16 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq101135 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq101134
       have r₂ := eq5390 x
       grind)
    | exact resolve eq101134 eq5390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101134
  have eq101136 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq101135
       have i₂ := eq5390 y
       grind)
    | exact superpose eq5390 eq101135
    | exact resolve eq101135 eq5390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101135
  have eq101751 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq101136
       grind)
    | exact superpose eq101136 eq10
    | exact resolve eq10 eq101136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101136
  have eq101897 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq101751
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq101751
    | exact resolve eq101751 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101751
  have eq101930 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101897
       grind)
    | exact superpose eq101897 eq16
    | exact resolve eq16 eq101897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101897
  have eq101931 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq101930
       have r₂ := eq5390 x
       grind)
    | exact resolve eq101930 eq5390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5390 eq101930
  have eq102803 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq101931
       grind)
    | exact superpose eq101931 eq10
    | exact resolve eq10 eq101931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101931
  have eq102957 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq102803
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq102803
    | exact resolve eq102803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102803
  have eq102958 : y = (M.op y y) := by grind
  clear eq102957
  have eq102981 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq102958
       grind)
    | exact superpose eq102958 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq102958
       grind)
    | exact resolve eq12 eq102958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103004 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5332 y X0
       have i₂ := eq102958
       grind)
    | exact superpose eq102958 eq5332
    | (have j0 := eq5332 y X0
       grind)
    | exact resolve eq5332 eq102958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5332 eq102958
  have eq103108 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq103004 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103004
  have eq103111 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq102981 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102981
  have eq107265 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq103108 (σ X0)
       grind)
    | exact superpose eq103108 eq15
    | exact resolve eq15 eq103108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103108
  have eq107426 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq107265 X0
       have i₂ := eq103111 X0
       grind)
    | exact superpose eq103111 eq107265
    | exact resolve eq107265 eq103111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103111 eq107265
  have eq113224 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq107426 x
       grind)
    | exact superpose eq107426 eq16
    | (have r₁ := eq16
       have r₂ := eq107426 x
       grind)
    | exact resolve eq16 eq107426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107426
  have eq113401 : False := by grind
  exact eq113401
