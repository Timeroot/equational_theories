import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyy_pxy_y_pxy_Equation723 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X1 (M.op (M.op X2 X0) X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op X0 (M.op (M.op X2 X0) X0))
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op (M.op X1 X0) X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq72 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) X1
       have i₂ := eq62 (M.op (M.op X1 X2) X2) X3 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X2) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X0 X1 X2 x
       have i₂ := eq72 (M.op (M.op X1 X2) X2) x X0
       grind)
    | exact superpose eq72 eq77
    | exact resolve eq77 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq79 : ∀ X1 X2 : G, (M.op (M.op (M.op X1 X2) X2) (M.op X2 (M.op (M.op X1 X2) X2))) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq78 x X1 X2
       have i₂ := eq72 X2 x X1
       grind)
    | exact superpose eq72 eq78
    | exact resolve eq78 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq78
  have eq161 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ X0 ∨ (k (M.op (M.op X1 X0) X0) (M.op X0 (M.op (M.op X1 X0) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X1 x) x) (M.op x (M.op (M.op X1 x) x))
       have i₂ := eq79 X1 x
       grind)
    | exact superpose eq79 eq12
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X0 X1) X1)) ∨ (k (M.op X2 (M.op (M.op X0 X1) X1)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op (M.op X2 X0) X0)) X0
       have i₂ := eq62 X0 X1 X2
       grind)
    | exact superpose eq62 eq13
    | (have j0 := eq13 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq165 (τ X0)
       grind)
    | exact superpose eq165 eq17
    | (have j1 := eq165 (τ X0)
       grind)
    | exact resolve eq17 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq178 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq177
    | (have j0 := eq177 X0
       grind)
    | exact resolve eq177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq196 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) (τ X0)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq12
    | (have j1 := eq178 (τ X0)
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq178 X0
       grind)
    | exact resolve eq12 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq199 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq196 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq200 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq199 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq199
    | (have j0 := eq199 X0
       grind)
    | exact resolve eq199 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq213 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq200 X0
       grind)
    | exact superpose eq200 eq11
    | (have j1 := eq200 X0
       grind)
    | exact resolve eq11 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq214 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq213 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq213
    | (have j0 := eq213 X0
       grind)
    | exact resolve eq213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq215 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq214 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq412 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X2 X1) = X2 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X2 X1
       grind)
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X2 X1
       have j1 := eq14 X2 X1
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq437 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq437 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq455 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq452 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq452 (k X1 X1) X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq452 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq452 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq460 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq454 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq454 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq454 X0 (M.op (M.op X0 X0) X1)
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq454 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq454 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq462 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq412 X0 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | (have r₁ := eq412 (M.op X2 X1) X1 X2
       have r₂ := eq12 (M.op X2 X1) X1
       grind)
    | (have r₁ := eq412 X0 X1 (M.op X0 X1)
       have r₂ := eq12 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq412 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq412 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq464 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq460 X0 X1
       have j1 := eq455 X1 X0
       grind)
    | (have r₁ := eq460 X1 X0
       have r₂ := eq455 X0 X1
       grind)
    | (have r₁ := eq460 X0 (M.op X1 X1)
       have r₂ := eq455 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq460 (M.op X1 X1) X1
       have r₂ := eq455 (k X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq460 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq465 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq462 X0 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | (have r₁ := eq462 (M.op X2 X1) X1 X2
       have r₂ := eq12 (M.op X2 X1) X1
       grind)
    | (have r₁ := eq462 X0 X1 (M.op X0 X1)
       have r₂ := eq12 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq462 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq462 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq467 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq455 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq474 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq467 (σ X0)
       grind)
    | exact superpose eq467 eq22
    | exact resolve eq22 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq467 (τ X0)
       grind)
    | exact superpose eq467 eq18
    | exact resolve eq18 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq467
  have eq480 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq464 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq464
    | exact resolve eq464 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq464 X1 (τ X0)
       grind)
    | exact superpose eq464 eq17
    | (have j1 := eq464 X1 (τ X0)
       grind)
    | exact resolve eq17 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq510 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq464 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq520 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ X1 ∨ (k (M.op X2 (M.op (M.op X0 X1) X1)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq510 (M.op X2 (M.op (M.op X0 X1) X1)) X1
       have i₂ := eq62 X1 X2 X0
       grind)
    | exact superpose eq62 eq510
    | (have j0 := eq510 (M.op X0 X1) X1
       grind)
    | exact resolve eq510 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq504 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq504
    | exact resolve eq504 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq660 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq624
    | (have j0 := eq624 X0 X1
       grind)
    | exact resolve eq624 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq721 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 (M.op X0 (M.op (M.op X1 X0) X0)))) = (M.op X2 (M.op X2 (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq721 (M.op X0 (M.op (M.op X1 X0) X0)) (M.op (M.op X1 X0) X0) X2
       have i₂ := eq79 X1 X0
       grind)
    | exact superpose eq79 eq721
    | exact resolve eq721 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq750 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq721 X1 x X3
       have i₂ := eq721 X1 x X0
       grind)
    | exact superpose eq721 eq721
    | exact resolve eq721 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 X1 X2
       have i₂ := eq721 X1 X2 X0
       grind)
    | exact superpose eq721 eq62
    | exact resolve eq62 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq721 X1 x X0
       grind)
    | exact superpose eq721 eq9
    | exact resolve eq9 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq760 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 x
       have i₂ := eq721 X1 x X0
       grind)
    | exact superpose eq721 eq64
    | exact resolve eq64 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq721
  have eq791 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) = (M.op X2 (M.op X2 (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq749 X0 X1 X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq749
    | exact resolve eq749 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq793 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X0) = (M.op X2 (M.op X2 (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq791 X0 X1 X2
       have i₂ := eq62 X0 X0 X1
       grind)
    | exact superpose eq62 eq791
    | exact resolve eq791 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq796 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) X0)) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq758 X1 (M.op X1 (M.op (M.op X2 X0) X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq758
    | exact resolve eq758 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq758 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq758 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq758
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq758 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq806 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq758 X0 (M.op X0 X0)
       have i₂ := eq758 X0 X0
       grind)
    | exact superpose eq758 eq758
    | exact resolve eq758 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq758 X0 X1
       grind)
    | exact superpose eq758 eq62
    | exact resolve eq62 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq823 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq813 X1 X0 X2
       have i₂ := eq758 X0 X1
       grind)
    | exact superpose eq758 eq813
    | exact resolve eq813 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq832 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq474 X0
       have i₂ := eq806 (σ X0)
       grind)
    | exact superpose eq806 eq474
    | exact resolve eq474 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq833 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq475 X0
       have i₂ := eq806 (τ X0)
       grind)
    | exact superpose eq806 eq475
    | exact resolve eq475 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq837 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq802 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq802 X0 X0
       have r₂ := eq12 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq802 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq802 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq900 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq806 X1
       have i₂ := eq14 X1 X1
       grind)
    | (have i₁ := eq806 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq806
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq806 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1 X0
       have i₂ := eq806 X0
       grind)
    | exact superpose eq806 eq62
    | exact resolve eq62 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq806 X0
       grind)
    | exact superpose eq806 eq9
    | exact resolve eq9 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq927 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq900 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq900 X0 X1
       have r₂ := eq12 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq900 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq900 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq952 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X1 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq760 X1 (M.op X1 (M.op X0 X0))
       have i₂ := eq905 X0 X1
       grind)
    | exact superpose eq905 eq760
    | exact resolve eq760 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq980 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op (M.op X3 X0) X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq750 X1 (M.op X2 (M.op (M.op X3 X0) X0)) X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq750
    | exact resolve eq750 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq982 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq750 X1 (M.op X2 (M.op X0 X0)) X2
       have i₂ := eq905 X0 X2
       grind)
    | exact superpose eq905 eq750
    | exact resolve eq750 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq983 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq750 X1 (M.op X2 (M.op X2 X0)) X0
       have i₂ := eq758 X2 X0
       grind)
    | exact superpose eq758 eq750
    | exact resolve eq750 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq986 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X1))) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq750 X2 (M.op X3 X1) X3
       have i₂ := eq750 X3 X1 X0
       grind)
    | (have i₁ := eq750 X2 (M.op X3 X1) X3
       have i₂ := eq750 X0 X1 X3
       grind)
    | exact superpose eq750 eq750
    | exact resolve eq750 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1032 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X3) X3)) = (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X2 X3) X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X3 X3 X1 X2
       have i₂ := eq750 X3 (M.op X1 (M.op (M.op X2 X3) X3)) X0
       grind)
    | (have i₁ := eq61 X3 X3 X1 X2
       have i₂ := eq750 X0 (M.op X1 (M.op (M.op X2 X3) X3)) X3
       grind)
    | exact superpose eq750 eq61
    | exact resolve eq61 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1040 : ∀ X0 X1 X2 : G, (M.op X2 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X2 X1) = (k X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq510 X2 (M.op X2 X1)
       have i₂ := eq750 X2 X1 X0
       grind)
    | (have i₁ := eq510 X2 (M.op X2 X1)
       have i₂ := eq750 X0 X1 X2
       grind)
    | exact superpose eq750 eq510
    | (have j0 := eq510 X2 (M.op X2 X1)
       grind)
    | exact resolve eq510 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1054 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq793 X0 X1 x
       have i₂ := eq980 X0 x X0 X1
       grind)
    | exact superpose eq980 eq793
    | exact resolve eq793 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq1055 : ∀ X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X3) X3)) = (M.op X3 (M.op X1 X3)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1032 x X1 X2 X3
       have i₂ := eq980 X3 x X1 X2
       grind)
    | exact superpose eq980 eq1032
    | exact resolve eq1032 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1066 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq1055 X1 x X0
       grind)
    | exact superpose eq1055 eq9
    | exact resolve eq9 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1068 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1 X2
       have i₂ := eq1055 X1 X2 X0
       grind)
    | exact superpose eq1055 eq62
    | exact resolve eq62 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1073 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X2 X1)) ∨ (M.op X1 X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k (M.op X2 (M.op (M.op X0 X1) X1)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq164 X0 X1 X2
       have i₂ := eq1055 X2 X0 X1
       grind)
    | exact superpose eq1055 eq164
    | (have j0 := eq164 X0 X1 X2
       grind)
    | exact resolve eq164 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq1076 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 X1)) X1) = X1 ∨ (M.op (M.op X0 X1) X1) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq520 X0 X1 X2
       have i₂ := eq1055 X2 X0 X1
       grind)
    | exact superpose eq1055 eq520
    | (have j0 := eq520 X0 X1 X2
       grind)
    | exact resolve eq520 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq1086 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq796 x X1 x
       have i₂ := eq1055 X1 x x
       grind)
    | exact superpose eq1055 eq796
    | exact resolve eq796 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq1094 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq980 X0 X1 X2 x
       have i₂ := eq1055 X2 x X0
       grind)
    | exact superpose eq1055 eq980
    | exact resolve eq980 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq1100 : ∀ X0 X1 : G, (k (M.op (M.op X1 X0) X0) (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op (M.op X1 X0) X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq161 X0 X1
       have i₂ := eq1055 X0 X1 X0
       grind)
    | exact superpose eq1055 eq161
    | (have j0 := eq161 X0 X1
       grind)
    | exact resolve eq161 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq1142 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq757 X0 X1 x
       have i₂ := eq1054 X1 x
       grind)
    | exact superpose eq1054 eq757
    | exact resolve eq757 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq1147 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq927 X0 X1
       have i₂ := eq1054 X1 X0
       grind)
    | exact superpose eq1054 eq927
    | (have j0 := eq927 X0 X1
       grind)
    | exact resolve eq927 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq1148 : ∀ X1 X3 : G, (M.op X3 (M.op X1 X3)) = (M.op X1 (M.op X3 X3)) := by
    intro X1 X3
    first
    | (have i₁ := eq1055 X1 x X3
       have i₂ := eq1054 X3 x
       grind)
    | exact superpose eq1054 eq1055
    | exact resolve eq1055 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1167 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op (M.op X1 X0) X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1100 X0 X1
       have i₂ := eq1054 X0 X1
       grind)
    | exact superpose eq1054 eq1100
    | (have j0 := eq1100 X0 X1
       grind)
    | exact resolve eq1100 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1171 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1086 X0 X1
       have i₂ := eq1054 (M.op X1 X0) X0
       grind)
    | exact superpose eq1054 eq1086
    | exact resolve eq1086 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1178 : ∀ X1 X2 : G, (M.op X1 X1) ≠ X1 ∨ (k (M.op X1 (M.op X2 X1)) X1) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq1076 x X1 X2
       have i₂ := eq1054 X1 x
       grind)
    | exact superpose eq1054 eq1076
    | (have j0 := eq1076 x X1 X2
       grind)
    | exact resolve eq1076 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1181 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X2 X1)) ∨ (k (M.op X2 (M.op (M.op X0 X1) X1)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1073 X0 X1 X2
       grind)
    | (have r₁ := eq1073 X1 X0 X2
       have r₂ := eq1054 X0 X1
       grind)
    | exact resolve eq1073 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1184 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1068 X0 X1 x
       have i₂ := eq1054 X0 x
       grind)
    | exact superpose eq1054 eq1068
    | exact resolve eq1068 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1191 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1167 X0 x
       have i₂ := eq1054 X0 x
       grind)
    | exact superpose eq1054 eq1167
    | (have j0 := eq1167 X0 x
       grind)
    | exact resolve eq1167 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1205 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 (M.op X2 X1)) ∨ (k (M.op X2 (M.op (M.op X0 X1) X1)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1181 X0 X1 X2
       have i₂ := eq1054 X1 X0
       grind)
    | exact superpose eq1054 eq1181
    | (have j0 := eq1181 X0 X1 X2
       grind)
    | exact resolve eq1181 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181
  have eq1215 : ∀ X1 X2 : G, (k (M.op X2 (M.op X1 X1)) X1) = X1 ∨ (M.op X1 X1) = (M.op X1 (M.op X2 X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq1205 x X1 X2
       have i₂ := eq1054 X1 x
       grind)
    | exact superpose eq1054 eq1205
    | (have j0 := eq1205 x X1 X2
       grind)
    | exact resolve eq1205 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054 eq1205
  have eq1225 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1066 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq1066 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq1066
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq1066 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1244 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1225 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1225 X0 X0
       have r₂ := eq12 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq1225 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1225 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1249 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1184 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq1066 X0 X1
       grind)
    | exact superpose eq1066 eq1184
    | exact resolve eq1184 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1265 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1066 X0 (M.op X0 (M.op X1 X0))
       have i₂ := eq1184 X0 X1
       grind)
    | exact superpose eq1184 eq1066
    | exact resolve eq1066 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1276 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1249 X0 X1
       have i₂ := eq1184 X0 X1
       grind)
    | exact superpose eq1184 eq1249
    | exact resolve eq1249 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq1285 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1276 X0 X1
       have i₂ := eq1171 (M.op X1 X0) X0
       grind)
    | exact superpose eq1171 eq1276
    | exact resolve eq1276 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1287 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1285 X0 X1
       have i₂ := eq1148 X0 (M.op X1 X0)
       grind)
    | exact superpose eq1148 eq1285
    | exact resolve eq1285 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1288 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1287 X0 X1
       have i₂ := eq1171 X0 X1
       grind)
    | exact superpose eq1171 eq1287
    | exact resolve eq1287 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq1366 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X1 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq510 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq1142 X1 X0
       grind)
    | exact superpose eq1142 eq510
    | (have j0 := eq510 X0 X0
       grind)
    | exact resolve eq510 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1372 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1066 X0 (M.op X1 (M.op X1 X0))
       have i₂ := eq1142 X1 X0
       grind)
    | exact superpose eq1142 eq1066
    | exact resolve eq1066 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1537 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X2 X0)) = (M.op X0 (M.op X3 (M.op X3 (M.op X2 (M.op X2 X0))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq823 (M.op X2 (M.op X2 X0)) X3 (M.op x X0)
       have i₂ := eq823 X0 X2 x
       grind)
    | exact superpose eq823 eq823
    | exact resolve eq823 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1538 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq823 (M.op X2 (M.op X0 X0)) X2 X1
       have i₂ := eq905 X0 X2
       grind)
    | exact superpose eq905 eq823
    | exact resolve eq823 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1569 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq750 X1 (M.op X2 (M.op X2 X0)) (M.op X3 X0)
       have i₂ := eq823 X0 X2 X3
       grind)
    | exact superpose eq823 eq750
    | exact resolve eq750 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1636 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X1 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq750 X2 (M.op X0 X1) X1
       have i₂ := eq1148 X0 X1
       grind)
    | (have i₁ := eq750 X0 (M.op x x) X1
       have i₂ := eq1148 X1 x
       grind)
    | exact superpose eq1148 eq750
    | exact resolve eq750 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1644 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1184 (M.op X0 X1) X1
       have i₂ := eq1148 X0 X1
       grind)
    | (have i₁ := eq1184 (M.op x x) X1
       have i₂ := eq1148 X1 x
       grind)
    | exact superpose eq1148 eq1184
    | exact resolve eq1184 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1664 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1066 (M.op X0 X0) X1
       have i₂ := eq1148 X1 X0
       grind)
    | (have i₁ := eq1066 (M.op X1 x) x
       have i₂ := eq1148 X1 x
       grind)
    | exact superpose eq1148 eq1066
    | exact resolve eq1066 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1676 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1664 X0 X1
       have i₂ := eq1288 X0 X1
       grind)
    | exact superpose eq1288 eq1664
    | exact resolve eq1664 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664
  have eq1692 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1644 X0 X1
       have i₂ := eq1538 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq1538 eq1644
    | exact resolve eq1644 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538 eq1644
  have eq1808 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = X1 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1244 X1 X2
       have i₂ := eq750 X1 X1 X0
       grind)
    | (have i₁ := eq1244 X1 X2
       have i₂ := eq750 X0 X1 X1
       grind)
    | exact superpose eq750 eq1244
    | (have j0 := eq1244 X1 X2
       grind)
    | exact resolve eq1244 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1887 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1265 (M.op X0 X0) X1
       have i₂ := eq1148 X1 X0
       grind)
    | (have i₁ := eq1265 (M.op X1 x) x
       have i₂ := eq1148 X1 x
       grind)
    | exact superpose eq1148 eq1265
    | exact resolve eq1265 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq1961 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1887 X0 X1
       have i₂ := eq905 X0 (M.op X0 X0)
       grind)
    | exact superpose eq905 eq1887
    | exact resolve eq1887 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887
  have eq1976 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 (M.op X1 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1961 X0 X1
       have i₂ := eq1288 X0 X1
       grind)
    | exact superpose eq1288 eq1961
    | exact resolve eq1961 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288 eq1961
  have eq2148 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq983 X2 X1 X1
       have i₂ := eq750 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq983 X2 X1 X1
       have i₂ := eq750 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq750 eq983
    | exact resolve eq983 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2367 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1094 X2 X2 X1
       have i₂ := eq750 X2 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq1094 X2 X2 X1
       have i₂ := eq750 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq750 eq1094
    | exact resolve eq1094 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2397 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 (M.op X1 (M.op X0 X1))))) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq750 X2 (M.op X3 (M.op X1 (M.op X0 X1))) X3
       have i₂ := eq1094 X1 X3 X0
       grind)
    | exact superpose eq1094 eq750
    | exact resolve eq750 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2400 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X3 (M.op X3 (M.op X2 (M.op X1 (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq823 (M.op X2 (M.op X1 (M.op X0 X1))) X3 X2
       have i₂ := eq1094 X1 X2 X0
       grind)
    | exact superpose eq1094 eq823
    | exact resolve eq823 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823 eq1094
  have eq2418 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2400 X0 X1 X2 x
       have i₂ := eq2397 X0 X1 x X2
       grind)
    | exact superpose eq2397 eq2400
    | exact resolve eq2400 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397 eq2400
  have eq2646 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X2 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1372 X1 X2
       have i₂ := eq750 X1 X1 X0
       grind)
    | (have i₁ := eq1372 X1 X2
       have i₂ := eq750 X0 X1 X1
       grind)
    | exact superpose eq750 eq1372
    | exact resolve eq1372 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq3351 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1676 X1 X0
       have i₂ := eq1148 X0 X1
       grind)
    | (have i₁ := eq1676 x x
       have i₂ := eq1148 x x
       grind)
    | exact superpose eq1148 eq1676
    | exact resolve eq1676 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676
  have eq3638 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X1 (M.op X2 (M.op X2 X0)))) = (M.op (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X0 X0))) (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1976 (M.op X1 (M.op X2 (M.op X2 X0))) X1
       have i₂ := eq983 X0 X1 X2
       grind)
    | exact superpose eq983 eq1976
    | exact resolve eq1976 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976
  have eq3751 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X1 (M.op X2 (M.op X2 X0)))) = (M.op X0 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3638 X0 X1 X2
       have i₂ := eq905 X0 (M.op X1 (M.op X2 (M.op X2 X0)))
       grind)
    | exact superpose eq905 eq3638
    | exact resolve eq3638 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3638
  have eq3782 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op X1 (M.op X2 (M.op X2 X0)))) = (M.op X0 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3751 X0 X1 X2
       have i₂ := eq1171 (M.op X2 (M.op X2 X0)) X1
       grind)
    | exact superpose eq1171 eq3751
    | exact resolve eq3751 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3751
  have eq3798 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X2 (M.op X2 X0)))) = (M.op X0 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3782 X0 X1 X2
       have i₂ := eq2418 X2 (M.op X2 X0) X1
       grind)
    | exact superpose eq2418 eq3782
    | exact resolve eq3782 eq2418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3782
  have eq3806 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X0) (M.op X2 X0)))) = (M.op X0 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3798 X0 X1 X2
       have i₂ := eq1148 X2 (M.op X2 X0)
       grind)
    | exact superpose eq1148 eq3798
    | exact resolve eq3798 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3798
  have eq3812 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 (M.op X2 X0)))) = (M.op X0 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3806 X0 X1 X2
       have i₂ := eq1171 X0 X2
       grind)
    | exact superpose eq1171 eq3806
    | exact resolve eq3806 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3806
  have eq3816 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3812 X0 X1 X2
       have i₂ := eq1066 X0 X2
       grind)
    | exact superpose eq1066 eq3812
    | exact resolve eq3812 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3812
  have eq3897 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq905 X2 X3
       have i₂ := eq2148 X1 X0 X2
       grind)
    | exact superpose eq2148 eq905
    | exact resolve eq905 eq2148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3938 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op X0 (M.op X1 (M.op X1 (M.op X0 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1692 X2 X3
       have i₂ := eq2148 X1 X0 (M.op X2 X3)
       grind)
    | exact superpose eq2148 eq1692
    | exact resolve eq1692 eq2148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq5456 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op X2 (M.op X2 (M.op X3 (M.op X0 (M.op X1 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq750 X2 (M.op X3 (M.op X0 (M.op X1 X1))) X3
       have i₂ := eq982 X1 X3 X0
       grind)
    | exact superpose eq982 eq750
    | exact resolve eq750 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5461 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 (M.op X0 X1)))) = (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq983 (M.op X2 (M.op X0 (M.op X1 X1))) X3 X2
       have i₂ := eq982 X1 X2 X0
       grind)
    | exact superpose eq982 eq983
    | exact resolve eq983 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5503 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 (M.op X0 X1)))) = (M.op (M.op X0 (M.op X1 X1)) (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5461 X0 X1 X2 X3
       have i₂ := eq1171 (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq1171 eq5461
    | exact resolve eq5461 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5461
  have eq5570 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 (M.op X0 X1)))) = (M.op X2 (M.op (M.op X1 X1) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5503 X0 X1 X2 X3
       have i₂ := eq2418 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq2418 eq5503
    | exact resolve eq5503 eq2418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5503
  have eq5616 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 (M.op X0 X1)))) = (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5570 X0 X1 X2 X3
       have i₂ := eq2418 X1 X1 X0
       grind)
    | exact superpose eq2418 eq5570
    | exact resolve eq5570 eq2418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418 eq5570
  have eq7108 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq465 (σ x) (σ y) X0
       grind)
    | (have i₁ := eq16
       have i₂ := eq465 X0 (σ y) (σ x)
       grind)
    | exact superpose eq465 eq16
    | (have j1 := eq465 (σ x) (σ y) (σ x)
       grind)
    | exact resolve eq16 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq7170 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7108 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7108
    | (have j0 := eq7108 X0
       grind)
    | exact resolve eq7108 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7108
  have eq8505 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op X4 X2))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq986 X4 X2 x X0
       have i₂ := eq986 X1 X2 x X0
       grind)
    | (have i₁ := eq986 X0 X1 X0 X0
       have i₂ := eq986 X0 X1 X2 X0
       grind)
    | exact superpose eq986 eq986
    | exact resolve eq986 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12751 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (M.op (σ X1) (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1066 (σ X1) (σ X0)
       have i₂ := eq421 X0 X1
       grind)
    | exact superpose eq421 eq1066
    | (have j1 := eq421 X0 X1
       grind)
    | exact resolve eq1066 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq19307 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq480 x y
       grind)
    | exact superpose eq480 eq16
    | (have j1 := eq480 x y
       grind)
    | exact resolve eq16 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19368 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (M.op (σ X1) (σ (k X0 X1)))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1066 (σ X1) (σ X0)
       have i₂ := eq480 X0 X1
       grind)
    | exact superpose eq480 eq1066
    | (have j1 := eq480 X0 X1
       grind)
    | exact resolve eq1066 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq21516 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 (M.op X1 (M.op X0 (M.op X2 X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3897 X2 X0 X3 X2
       have i₂ := eq986 X1 (M.op X0 (M.op X2 X3)) X2 X0
       grind)
    | (have i₁ := eq3897 X0 X0 X2 X3
       have i₂ := eq986 X0 (M.op X0 (M.op X0 X2)) X2 X3
       grind)
    | exact superpose eq986 eq3897
    | exact resolve eq3897 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq40378 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op X2 X2))))) X2) = X2 ∨ (M.op X2 X2) = (M.op X2 (M.op (M.op X3 (M.op X2 X2)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1215 X2 (M.op X3 (M.op X2 X2))
       have i₂ := eq1569 (M.op X2 X2) X0 X1 X3
       grind)
    | exact superpose eq1569 eq1215
    | (have j0 := eq1215 X2 (M.op X3 (M.op X2 X2))
       grind)
    | exact resolve eq1215 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215 eq1569
  have eq40423 : ∀ X1 X2 X3 : G, (k (M.op X1 (M.op X1 X2)) X2) = X2 ∨ (M.op X2 X2) = (M.op X2 (M.op (M.op X3 (M.op X2 X2)) X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq40378 x X1 X2 X3
       have i₂ := eq5456 X1 X2 x X1
       grind)
    | exact superpose eq5456 eq40378
    | (have j0 := eq40378 x X1 X2 X3
       grind)
    | exact resolve eq40378 eq5456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5456 eq40378
  have eq40490 : ∀ X1 X2 : G, (M.op X2 X2) = (M.op X2 (M.op X2 X2)) ∨ (k (M.op X1 (M.op X1 X2)) X2) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq40423 X1 X2 x
       have i₂ := eq903 X2 x
       grind)
    | exact superpose eq903 eq40423
    | (have j0 := eq40423 X1 X2 x
       grind)
    | exact resolve eq40423 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq40423
  have eq42192 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) ≠ X2 ∨ (k (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) (M.op X2 (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1191 X0
       have i₂ := eq983 X0 X1 X2
       grind)
    | exact superpose eq983 eq1191
    | exact resolve eq1191 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq42211 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) (M.op X1 (M.op X1 X2))) = X2 ∨ (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) ≠ X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42192 X0 X1 X2
       have i₂ := eq1537 X2 X1 X0
       grind)
    | exact superpose eq1537 eq42192
    | (have j0 := eq42192 X0 X1 X2
       grind)
    | exact resolve eq42192 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537 eq42192
  have eq42268 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq19307
       have i₂ := eq1147 x y
       grind)
    | exact superpose eq1147 eq19307
    | (have j1 := eq1147 x y
       grind)
    | exact resolve eq19307 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147
  have eq42273 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq19307
       have i₂ := eq660 x y
       grind)
    | exact superpose eq660 eq19307
    | (have j1 := eq660 x y
       grind)
    | (have r₁ := eq19307
       have r₂ := eq660 x y
       grind)
    | exact resolve eq19307 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq19307
  have eq42274 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by grind
  clear eq42273
  have eq42279 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq42268
  have eq42718 : (M.op x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq42274
       grind)
    | exact superpose eq42274 eq10
    | exact resolve eq10 eq42274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42274
  have eq42762 : y = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq42718
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq42718
    | exact resolve eq42718 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42718
  have eq42763 : y = (k x y) := by
    first
    | (have j1 := eq510 x y
       grind)
    | (have r₁ := eq42762
       have r₂ := eq510 x y
       grind)
    | exact resolve eq42762 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq42762
  have eq42764 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7170 X0
       have i₂ := eq42763
       grind)
    | exact superpose eq42763 eq7170
    | (have j0 := eq7170 X0
       grind)
    | exact resolve eq7170 eq42763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7170
  have eq42984 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq22 X0 (M.op x y)
       have i₂ := eq42279
       grind)
    | exact superpose eq42279 eq22
    | exact resolve eq22 eq42279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42279
  have eq43014 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (k (τ X0) y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq42984 X0
       have i₂ := eq22 X0 y
       grind)
    | exact superpose eq22 eq42984
    | exact resolve eq42984 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq42984
  have eq44368 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1)))) ∨ (M.op X0 (M.op X0 X1)) = (k X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq837 X0 (M.op X0 X1)
       have i₂ := eq750 X0 X1 x
       grind)
    | (have i₁ := eq837 x (M.op x X1)
       have i₂ := eq750 X0 X1 x
       grind)
    | exact superpose eq750 eq837
    | exact resolve eq837 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750 eq837
  have eq44756 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X0 (M.op X0 (M.op X1 (M.op X1 X1)))) ∨ (M.op X0 (M.op X0 X1)) = (k X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44368 X0 X1 X2
       have i₂ := eq5616 X0 X1 X0 (M.op X2 X1)
       grind)
    | (have i₁ := eq44368 X1 X1 X2
       have i₂ := eq5616 (M.op X2 X1) X1 (M.op X2 X1) x
       grind)
    | exact superpose eq5616 eq44368
    | (have j0 := eq44368 X0 X1 X2
       grind)
    | exact resolve eq44368 eq5616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5616 eq44368
  have eq44826 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 X1) ∨ (M.op X0 (M.op X0 X1)) = (k X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44756 X0 X1 X2
       have i₂ := eq982 X1 X0 X1
       grind)
    | exact superpose eq982 eq44756
    | (have j0 := eq44756 X0 X1 X2
       grind)
    | exact resolve eq44756 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982 eq44756
  have eq243870 : ∀ X0 X1 : G, (M.op X1 (k X0 (M.op X0 X1))) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq905 X1 X1
       have i₂ := eq44826 X1 X1 X0
       grind)
    | exact superpose eq44826 eq905
    | (have j1 := eq44826 X0 X1 X0
       grind)
    | exact resolve eq905 eq44826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq44826
  have eq271171 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0)))))) ∨ (k (M.op X3 (M.op X3 X0)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21516 X1 X2 X0 (M.op X0 X0)
       have i₂ := eq40490 X3 X0
       grind)
    | exact superpose eq40490 eq21516
    | (have j1 := eq40490 X3 X0
       grind)
    | exact resolve eq21516 eq40490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40490
  have eq271275 : ∀ X0 X3 : G, (M.op X0 X0) = X0 ∨ (k (M.op X3 (M.op X3 X0)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq271171 X0 x x X3
       have i₂ := eq21516 x x X0 X0
       grind)
    | exact superpose eq21516 eq271171
    | (have j0 := eq271171 X0 x x X3
       grind)
    | exact resolve eq271171 eq21516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21516 eq271171
  have eq271918 : ∀ X0 X3 : G, (k (M.op X3 (M.op X3 X0)) X0) = X0 := by
    intro X0 X3
    first
    | (have j0 := eq271275 X0 X3
       have j1 := eq1366 X0 X3
       grind)
    | (have r₁ := eq271275 X0 X3
       have r₂ := eq1366 X0 x
       grind)
    | exact resolve eq271275 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366 eq271275
  have eq272422 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) ≠ X2 ∨ (M.op X1 (M.op X1 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42211 X0 X1 X2
       have i₂ := eq271918 (M.op X1 (M.op X1 X2)) X0
       grind)
    | exact superpose eq271918 eq42211
    | (have j0 := eq42211 X0 X1 X2
       grind)
    | exact resolve eq42211 eq271918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42211
  have eq273073 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op X0 X0) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq271918 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq3816 X0 X0 X1
       grind)
    | exact superpose eq3816 eq271918
    | exact resolve eq271918 eq3816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273206 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1191 X0
       have i₂ := eq273073 X0 X0
       grind)
    | exact superpose eq273073 eq1191
    | (have j0 := eq1191 X0
       grind)
    | exact resolve eq1191 eq273073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq275920 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (M.op X1 (M.op X1 X0)) = (M.op (M.op X1 (M.op X1 X0)) X0) ∨ (M.op (M.op X1 (M.op X1 X0)) X0) = (k (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq273206 (M.op X0 (M.op X0 X1))
       have i₂ := eq1808 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq1808 eq273206
    | (have j1 := eq1808 X0 X0 (M.op X1 (M.op X1 X0))
       grind)
    | exact resolve eq273206 eq1808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1808 eq273206
  have eq275978 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (M.op (M.op X1 (M.op X1 X0)) X0) = (k (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq275920 X0 X1
       have j1 := eq12 (M.op X1 (M.op X1 X0)) X0
       grind)
    | (have r₁ := eq275920 X1 X1
       have r₂ := eq12 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq275920 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275920
  have eq276012 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) X0) = X0 ∨ (M.op X1 (M.op X1 X0)) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq275978 X0 X1
       have i₂ := eq271918 X0 X1
       grind)
    | exact superpose eq271918 eq275978
    | (have j0 := eq275978 X0 X1
       grind)
    | exact resolve eq275978 eq271918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275978
  have eq276035 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq276012 X0 X1
       have i₂ := eq1142 X1 X0
       grind)
    | exact superpose eq1142 eq276012
    | (have j0 := eq276012 X0 X1
       grind)
    | exact resolve eq276012 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142 eq276012
  have eq276357 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 (M.op X1 X0)) = (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq276035 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq3816 X0 X0 X1
       grind)
    | exact superpose eq3816 eq276035
    | (have j0 := eq276035 (M.op X1 (M.op X1 X0)) X1
       grind)
    | exact resolve eq276035 eq3816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816
  have eq276420 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq276357 X0 X1
       have i₂ := eq2646 X1 X0 X1
       grind)
    | exact superpose eq2646 eq276357
    | (have j0 := eq276357 X0 X1
       grind)
    | exact resolve eq276357 eq2646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276357
  have eq294361 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0))))) ≠ X0 ∨ (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq276420 (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2)))) x
       have i₂ := eq3897 X0 X1 X2 x
       grind)
    | exact superpose eq3897 eq276420
    | exact resolve eq276420 eq3897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3897 eq276420
  have eq294460 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X2 (M.op X1 X0))) (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0))))) ≠ X0 ∨ (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq294361 X0 X1 X2
       have i₂ := eq1171 (M.op X2 (M.op X2 (M.op X1 X0))) X1
       grind)
    | exact superpose eq1171 eq294361
    | (have j0 := eq294361 X0 X1 X2
       grind)
    | exact resolve eq294361 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171 eq294361
  have eq294723 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X2 (M.op X1 X0))) (M.op X2 (M.op X2 (M.op X1 X0))))) ≠ X0 ∨ (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq294460 X0 X1 X2
       have i₂ := eq1148 X1 (M.op X2 (M.op X2 (M.op X1 X0)))
       grind)
    | exact superpose eq1148 eq294460
    | (have j0 := eq294460 X0 X1 X2
       grind)
    | exact resolve eq294460 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294460
  have eq294926 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq294723 X0 X1 X2
       have i₂ := eq2646 X2 (M.op X1 X0) X2
       grind)
    | exact superpose eq2646 eq294723
    | (have j0 := eq294723 X0 X1 X2
       grind)
    | exact resolve eq294723 eq2646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646 eq294723
  have eq299277 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12751 x y
       have i₂ := eq42763
       grind)
    | exact superpose eq42763 eq12751
    | (have j0 := eq12751 x y
       grind)
    | exact resolve eq12751 eq42763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12751
  have eq351224 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq43014 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq43014
    | exact resolve eq43014 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43014
  have eq351407 : y = (M.op y (k x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq243870 x y
       have i₂ := eq351224 x
       grind)
    | exact superpose eq351224 eq243870
    | (have j0 := eq243870 x y
       grind)
    | exact resolve eq243870 eq351224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243870
  have eq351452 : (M.op x (M.op y y)) = (k (M.op x (M.op y y)) y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq952 y x
       have i₂ := eq351224 (M.op x (M.op y y))
       grind)
    | exact superpose eq351224 eq952
    | exact resolve eq952 eq351224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952 eq351224
  have eq351508 : y = (M.op y (k x y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq351407
  have eq351555 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq351508
       have i₂ := eq42763
       grind)
    | exact superpose eq42763 eq351508
    | exact resolve eq351508 eq42763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42763 eq351508
  have eq352002 : y = (k (M.op y (M.op x y)) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq271918 y y
       have i₂ := eq351555
       grind)
    | exact superpose eq351555 eq271918
    | exact resolve eq271918 eq351555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271918 eq351555
  have eq352043 : y = (k (M.op y (M.op x y)) y) := by
    first
    | (have j1 := eq1178 y x
       grind)
    | (have r₁ := eq352002
       have r₂ := eq1178 y x
       grind)
    | exact resolve eq352002 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178 eq352002
  have eq352208 : y = (k (M.op x (M.op y y)) y) := by
    first
    | (have i₁ := eq352043
       have i₂ := eq1148 x y
       grind)
    | exact superpose eq1148 eq352043
    | exact resolve eq352043 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148 eq352043
  have eq352274 : y = (M.op x (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq351452
       have i₂ := eq352208
       grind)
    | exact superpose eq352208 eq351452
    | exact resolve eq351452 eq352208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351452 eq352208
  have eq354919 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1636 x y X0
       have i₂ := eq352274
       grind)
    | exact superpose eq352274 eq1636
    | exact resolve eq1636 eq352274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq355204 : ∀ X0 : G, (M.op y y) ≠ (M.op X0 (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq272422 X0 x (M.op y y)
       have i₂ := eq352274
       grind)
    | exact superpose eq352274 eq272422
    | exact resolve eq272422 eq352274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272422 eq352274
  have eq355222 : ∀ X0 : G, (M.op y y) ≠ (M.op X0 (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq355204 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355204
  have eq355430 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq354919 x
       have r₂ := eq355222 x
       grind)
    | exact resolve eq354919 eq355222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354919 eq355222
  have eq652317 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X0)) (M.op (σ (τ X1)) (σ (τ (k X0 X1))))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19368 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq19368
    | exact resolve eq19368 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq19368
  have eq653099 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X0)) (M.op (σ (τ X1)) (k X0 X1))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq652317 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq652317
    | (have j0 := eq652317 X0 X1
       grind)
    | exact resolve eq652317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652317
  have eq653315 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (M.op X1 (k X0 X1))) = X1 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq653099 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq653099
    | (have j0 := eq653099 X0 X1
       grind)
    | exact resolve eq653099 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653099
  have eq653364 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 X1))) = X1 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq653315 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq653315
    | (have j0 := eq653315 X0 X1
       grind)
    | exact resolve eq653315 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653315
  have eq653384 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ X1)) ∨ (M.op X0 (M.op X1 (k X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq653364 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq653364
    | (have j0 := eq653364 X0 X1
       grind)
    | exact resolve eq653364 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653364
  have eq653390 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 X1))) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq653384 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq653384
    | (have j0 := eq653384 X0 X1
       grind)
    | exact resolve eq653384 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653384
  have eq653646 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (k X1 X0) (k X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2148 X1 X0 (k X1 X0)
       have i₂ := eq653390 X1 X0
       grind)
    | exact superpose eq653390 eq2148
    | (have j1 := eq653390 X1 X0
       grind)
    | exact resolve eq2148 eq653390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148
  have eq653647 : ∀ X0 X1 : G, (M.op X0 (k X1 X0)) = (M.op (k X1 X0) (M.op X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2367 X1 X0 (k X1 X0)
       have i₂ := eq653390 X1 X0
       grind)
    | exact superpose eq653390 eq2367
    | (have j1 := eq653390 X1 X0
       grind)
    | exact resolve eq2367 eq653390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653718 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (k X1 X0)))) ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1040 X0 (M.op X1 (k X0 X1)) X0
       have i₂ := eq653390 X0 X1
       grind)
    | exact superpose eq653390 eq1040
    | (have j1 := eq653390 X1 X0
       grind)
    | exact resolve eq1040 eq653390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040 eq653390
  have eq654001 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (k X1 X0)))) ≠ X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq653718 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653718
  have eq656872 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (k X2 X0)))) ≠ X0 ∨ (k X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq654001 X0 X2 X0
       have i₂ := eq8505 X0 X0 (k X2 X0) X1
       grind)
    | (have i₁ := eq654001 X0 X2 X0
       have i₂ := eq8505 X0 X1 (k X2 X0) X0
       grind)
    | exact superpose eq8505 eq654001
    | (have j0 := eq654001 X0 X2 X2
       grind)
    | exact resolve eq654001 eq8505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8505 eq654001
  have eq667210 : ∀ X0 X1 : G, (M.op X0 (M.op (k X1 X0) (M.op X0 (M.op X1 X0)))) ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq656872 X0 (k X1 X0) X1
       have i₂ := eq653646 X0 X1
       grind)
    | exact superpose eq653646 eq656872
    | (have j0 := eq656872 X0 X1 X1
       have j1 := eq653646 X0 X1
       grind)
    | exact resolve eq656872 eq653646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653646 eq656872
  have eq667682 : ∀ X0 X1 : G, (M.op X0 (M.op (k X1 X0) (M.op X0 (M.op X1 X0)))) ≠ X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq667210 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667210
  have eq668609 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (k X1 X0) (M.op X2 (M.op X2 (M.op X0 (k X1 X0))))) ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3938 (k X1 X0) X2 X1 X0
       have i₂ := eq653647 X0 X1
       grind)
    | exact superpose eq653647 eq3938
    | (have j1 := eq653647 X0 X1
       grind)
    | exact resolve eq3938 eq653647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3938 eq653647
  have eq669429 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (k X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq668609 X0 X1 x
       have i₂ := eq2367 x X0 (k X1 X0)
       grind)
    | exact superpose eq2367 eq668609
    | (have j0 := eq668609 X0 X1 x
       grind)
    | exact resolve eq668609 eq2367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2367 eq668609
  have eq670206 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X0 (k X1 X0)))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3351 X1 X0
       have i₂ := eq669429 X0 X1
       grind)
    | exact superpose eq669429 eq3351
    | (have j1 := eq669429 X0 X1
       grind)
    | exact resolve eq3351 eq669429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3351 eq669429
  have eq681701 : ∀ X0 : G, (M.op X0 (M.op (τ (M.op (σ X0) (σ X0))) (M.op X0 (M.op (τ (M.op (σ X0) (σ X0))) X0)))) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq667682 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq832 X0
       grind)
    | exact superpose eq832 eq667682
    | exact resolve eq667682 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq667682
  have eq682473 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq681701 X0
       have i₂ := eq1066 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq1066 eq681701
    | (have j0 := eq681701 X0
       grind)
    | exact resolve eq681701 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066 eq681701
  have eq683441 : y ≠ (M.op x y) ∨ y = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq682473 y
       have i₂ := eq355430
       grind)
    | exact superpose eq355430 eq682473
    | (have j0 := eq682473 y
       grind)
    | exact resolve eq682473 eq355430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682473
  have eq692236 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ X0))) (M.op X0 (M.op X0 (σ (M.op (τ X0) (τ X0)))))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq670206 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq833 X0
       grind)
    | exact superpose eq833 eq670206
    | exact resolve eq670206 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq670206
  have eq693162 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq692236 X0
       have i₂ := eq758 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact superpose eq758 eq692236
    | (have j0 := eq692236 X0
       grind)
    | exact resolve eq692236 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692236
  have eq762119 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq693162 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq693162
    | exact resolve eq693162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693162
  have eq762434 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (k (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq42764 (σ y)
       have i₂ := eq762119 y
       grind)
    | exact superpose eq762119 eq42764
    | (have j1 := eq762119 y
       grind)
    | exact resolve eq42764 eq762119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42764
  have eq763042 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (k (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq762434
       have i₂ := eq355430
       grind)
    | exact superpose eq355430 eq762434
    | exact resolve eq762434 eq355430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762434
  have eq763043 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (k (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq763042
  have eq763099 : (σ (M.op y y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq763043
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq763043
    | exact resolve eq763043 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763043
  have eq763119 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq763099
       have i₂ := eq215 y
       grind)
    | exact superpose eq215 eq763099
    | exact resolve eq763099 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq763099
  have eq763120 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq763119
  have eq763123 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq763120
       have i₂ := eq355430
       grind)
    | exact superpose eq355430 eq763120
    | exact resolve eq763120 eq355430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763120
  have eq763426 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq276035 (σ y) (σ x)
       have i₂ := eq763123
       grind)
    | exact superpose eq763123 eq276035
    | (have j0 := eq276035 (σ y) x
       grind)
    | exact resolve eq276035 eq763123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276035
  have eq763509 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq763426
       have r₂ := eq763123
       grind)
    | exact resolve eq763426 eq763123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763123 eq763426
  have eq763706 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq762119 y
       have i₂ := eq763509
       grind)
    | exact superpose eq763509 eq762119
    | (have j0 := eq762119 y
       grind)
    | exact resolve eq762119 eq763509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762119 eq763509
  have eq764207 : (σ y) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq763706
  have eq764339 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq764207
       have i₂ := eq355430
       grind)
    | exact superpose eq355430 eq764207
    | exact resolve eq764207 eq355430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355430 eq764207
  have eq764340 : (σ (M.op x y)) = (σ y) := by grind
  clear eq764339
  have eq764390 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq764340
       grind)
    | exact superpose eq764340 eq16
    | exact resolve eq16 eq764340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764708 : (M.op x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq764340
       grind)
    | exact superpose eq764340 eq10
    | exact resolve eq10 eq764340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764340
  have eq764820 : y = (M.op x y) := by
    first
    | (have i₁ := eq764708
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq764708
    | exact resolve eq764708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764708
  have eq770396 : y ≠ y ∨ y = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq683441
       have i₂ := eq764820
       grind)
    | exact superpose eq764820 eq683441
    | (have r₁ := eq683441
       have r₂ := eq764820
       grind)
    | exact resolve eq683441 eq764820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683441 eq764820
  have eq771483 : y = (τ (M.op (σ y) (σ y))) := by grind
  clear eq770396
  have eq789637 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ y) (σ y))
       have i₂ := eq771483
       grind)
    | exact superpose eq771483 eq11
    | exact resolve eq11 eq771483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771483
  have eq789750 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq299277
       have i₂ := eq789637
       grind)
    | exact superpose eq789637 eq299277
    | exact resolve eq299277 eq789637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299277
  have eq789884 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq789750
       have r₂ := eq764390
       grind)
    | exact resolve eq789750 eq764390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789750
  have eq789916 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq789884
       have i₂ := eq789637
       grind)
    | exact superpose eq789637 eq789884
    | exact resolve eq789884 eq789637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789884
  have eq789935 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq789916
       have r₂ := eq764390
       grind)
    | exact resolve eq789916 eq764390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789916
  have eq789942 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq764390
       have i₂ := eq789935
       grind)
    | exact superpose eq789935 eq764390
    | exact resolve eq764390 eq789935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764390
  have eq789984 : (σ y) = (k (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq760 (σ x) (σ y)
       have i₂ := eq789935
       grind)
    | exact superpose eq789935 eq760
    | exact resolve eq760 eq789935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq790233 : (M.op (σ x) (σ x)) = (k (M.op (σ y) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq273073 (σ y) (σ x)
       have i₂ := eq789935
       grind)
    | exact superpose eq789935 eq273073
    | exact resolve eq273073 eq789935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273073
  have eq790247 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq294926 (σ y) (σ x) x
       have i₂ := eq789935
       grind)
    | exact superpose eq789935 eq294926
    | exact resolve eq294926 eq789935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294926 eq789935
  have eq790322 : (σ x) = (σ y) ∨ (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq790247 x
       have i₂ := eq758 x (σ x)
       grind)
    | exact superpose eq758 eq790247
    | exact resolve eq790247 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758 eq790247
  have eq790333 : (M.op (σ x) (σ x)) = (k (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq790233
       have i₂ := eq789637
       grind)
    | exact superpose eq789637 eq790233
    | exact resolve eq790233 eq789637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789637 eq790233
  have eq790604 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq790322
       have r₂ := eq789942
       grind)
    | exact resolve eq790322 eq789942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789942 eq790322
  have eq790611 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq790333
       have i₂ := eq789984
       grind)
    | exact superpose eq789984 eq790333
    | exact resolve eq790333 eq789984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789984 eq790333
  have eq790823 : False := by grind
  exact eq790823

/-- `Equation727`: `x = y ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation727 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law727 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law727.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq53 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq172 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq179 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq172 X0 X1
       have j1 := eq56 X0 X1
       grind)
    | (have r₁ := eq172 X0 X1
       have r₂ := eq56 X0 X1
       grind)
    | (have r₁ := eq172 X0 X0
       have r₂ := eq56 X0 X0
       grind)
    | exact resolve eq172 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq172
  have eq456 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq179 (σ X1) (σ X0)
       grind)
    | exact superpose eq179 eq15
    | exact resolve eq15 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq179 X1 X0
       grind)
    | exact superpose eq179 eq456
    | exact resolve eq456 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq456
  have eq466 : False := by grind
  exact eq466

/-- `Equation826`: `x = x ◇ ((x ◇ y) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation826 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law826 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law826.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
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
  have eq68 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq81 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq592
    | exact resolve eq592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq596 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq593
       have r₂ := eq27
       grind)
    | exact resolve eq593 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq598 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq596
    | exact resolve eq596 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq600 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq598
    | exact resolve eq598 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq612 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq600 eq68
    | (have r₁ := eq68
       have r₂ := eq600
       grind)
    | exact resolve eq68 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq600
  have eq617 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq612
  have eq687 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq617
       have r₂ := eq616
       grind)
    | exact resolve eq617 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq617
  have eq691 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq687 eq81
    | exact resolve eq81 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq699 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq691
    | exact resolve eq691 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq691
  have eq703 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq699
       have r₂ := eq67
       grind)
    | exact resolve eq699 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq706 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq703
       grind)
    | exact superpose eq703 eq74
    | exact resolve eq74 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq703
       grind)
    | exact superpose eq703 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq708 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq707
  have eq710 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq708
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq708
    | exact resolve eq708 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq711 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq710
  have eq712 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq706
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq706
    | exact resolve eq706 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq715 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq711
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq711
    | exact resolve eq711 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq719 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq715 eq51
    | (have r₁ := eq51
       have r₂ := eq715
       grind)
    | exact resolve eq51 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq721 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq719
  have eq731 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq712 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq732 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq731
  have eq736 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq732
    | exact resolve eq732 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq737 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq736
  have eq742 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq737
    | exact resolve eq737 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq750 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq742 eq27
    | exact resolve eq27 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq767 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq721 eq81
    | exact resolve eq81 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq778 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq767
    | exact resolve eq767 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq781 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq778
       have r₂ := eq50
       grind)
    | exact resolve eq778 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq787 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq781
       grind)
    | exact superpose eq781 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq788 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq787
  have eq790 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq788
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq788
    | exact resolve eq788 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq791 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq790
  have eq795 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq791
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq791
    | exact resolve eq791 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq791
  have eq797 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq795 eq20
    | exact resolve eq20 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq801 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq795 eq67
    | (have r₁ := eq67
       have r₂ := eq795
       grind)
    | exact resolve eq67 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq810 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq795
  have eq811 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq801
  have eq821 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq797
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq797
    | exact resolve eq797 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq882 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq821 eq750
    | (have r₁ := eq750
       have r₂ := eq821
       grind)
    | exact resolve eq750 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750 eq821
  have eq885 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq882
  have eq886 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq885
  have eq906 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq886 eq51
    | (have r₁ := eq51
       have r₂ := eq886
       grind)
    | exact resolve eq51 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq886
  have eq909 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq906
  have eq1030 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq909 eq81
    | exact resolve eq81 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq909
  have eq1045 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1030
    | exact resolve eq1030 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1030
  have eq1048 : y = (k y x) := by
    first
    | (have r₁ := eq1045
       have r₂ := eq50
       grind)
    | exact resolve eq1045 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1045
  have eq1053 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq1048
       grind)
    | exact superpose eq1048 eq74
    | exact resolve eq74 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1058 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1053
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1053
    | exact resolve eq1053 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1053
  have eq1071 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1058 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1071
  have eq1074 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1072
    | exact resolve eq1072 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1077 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1074
    | exact resolve eq1074 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1074
  have eq1130 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1077 eq68
    | (have r₁ := eq68
       have r₂ := eq1077
       grind)
    | exact resolve eq68 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1134 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1077
  have eq1135 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1130
  have eq1136 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1058 eq1135
    | exact resolve eq1135 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058 eq1135
  have eq1137 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1136
  have eq1189 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1137
       have r₂ := eq1134
       grind)
    | exact resolve eq1137 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134 eq1137
  have eq1193 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1189 eq27
    | exact resolve eq27 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1189
  have eq2436 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq811
       have r₂ := eq810
       grind)
    | exact resolve eq811 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq2437 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2436
       have i₂ := eq1048
       grind)
    | exact superpose eq1048 eq2436
    | exact resolve eq2436 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048 eq2436
  have eq2438 : x = (M.op x y) := by
    first
    | (have r₁ := eq2437
       have r₂ := eq810
       grind)
    | exact resolve eq2437 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq2437
  have eq2440 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2438 eq20
    | exact resolve eq20 eq2438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2438
  have eq2470 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2440
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2440
    | exact resolve eq2440 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2440
  have eq2472 : False := by grind
  exact eq2472

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq52 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq52 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq172 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq179 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq172 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq172 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq172 X0 X0
       have r₂ := eq55 X0 X0
       grind)
    | exact resolve eq172 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq172
  have eq385 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq179 (σ X1) (σ X0)
       grind)
    | exact superpose eq179 eq15
    | exact resolve eq15 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq385 X0 X1
       have i₂ := eq179 X1 X0
       grind)
    | exact superpose eq179 eq385
    | exact resolve eq385 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq385
  have eq395 : False := by grind
  exact eq395

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyx_pxx_pyx_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq18
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
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
  clear eq35
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq38
  have eq76 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
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
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq181 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq187 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq192 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq187
    | (have j0 := eq187 X0 X1
       grind)
    | exact resolve eq187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq193 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq205 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq193 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq193
    | (have j0 := eq193 X0 X1
       grind)
    | exact resolve eq193 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq193
  have eq206 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq205 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq500 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq206 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq206
    | exact resolve eq206 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq206 x y
       grind)
    | exact superpose eq206 eq16
    | (have j1 := eq206 x y
       grind)
    | exact resolve eq16 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq206 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq546 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq500 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq500
    | (have j0 := eq500 X0 X1
       grind)
    | exact resolve eq500 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq500
  have eq550 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq546
    | (have j0 := eq546 X0 X1
       grind)
    | exact resolve eq546 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq546
  have eq1643 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq550 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq550
    | exact resolve eq550 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq1783 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq1643 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq1643 X0 X1
       grind)
    | exact superpose eq1643 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq1643 X1 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq1643 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq1643 X0 X0
       grind)
    | exact resolve eq12 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1835 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1783 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq2924 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq510
       have i₂ := eq1835 x y
       grind)
    | exact superpose eq1835 eq510
    | (have j1 := eq1835 x y
       grind)
    | exact resolve eq510 eq1835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq1835
  have eq2927 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2924
  have eq3001 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq537 x y
       have i₂ := eq2927
       grind)
    | exact superpose eq2927 eq537
    | (have j0 := eq537 x y
       grind)
    | exact resolve eq537 eq2927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq2927
  have eq3015 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3001
  have eq3016 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3015
  have eq3046 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3016
       grind)
    | exact superpose eq3016 eq16
    | exact resolve eq16 eq3016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3049 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq76 x (σ y)
       have i₂ := eq3016
       grind)
    | exact superpose eq3016 eq76
    | (have j0 := eq76 x (σ y)
       grind)
    | (have r₁ := eq76 x (σ y)
       have r₂ := eq3016
       grind)
    | exact resolve eq76 eq3016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq3016
  have eq3052 : (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq3049
  have eq3054 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3052
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3052
    | exact resolve eq3052 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3052
  have eq3057 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq3046
       have i₂ := eq1643 y x
       grind)
    | exact superpose eq1643 eq3046
    | (have j1 := eq1643 y x
       grind)
    | exact resolve eq3046 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq3058 : (M.op x y) = (k x y) := by grind
  clear eq3057
  have eq3183 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3054
       have i₂ := eq3058
       grind)
    | exact superpose eq3058 eq3054
    | exact resolve eq3054 eq3058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3054 eq3058
  have eq3278 : False := by grind
  exact eq3278

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_pxx_x_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x y) ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq44
    | exact resolve eq44 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq73 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq50
    | exact resolve eq50 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq73
    | exact resolve eq73 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq72
    | exact resolve eq72 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq71
    | exact resolve eq71 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq80 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq80 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq585 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq592 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq585 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq585
    | exact resolve eq585 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq593 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq741 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq83 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2927 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq593 X0
       have j1 := eq741 X0
       grind)
    | (have r₁ := eq593 X0
       have r₂ := eq741 X0
       grind)
    | exact resolve eq593 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq741
  have eq27242 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq27242
    | exact resolve eq27242 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27242
  have eq27261 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq27250
       have r₂ := eq28
       grind)
    | exact resolve eq27250 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27250
  have eq27265 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq27261
    | exact resolve eq27261 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27261
  have eq27267 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27265 eq67
    | (have r₁ := eq67
       have r₂ := eq27265
       grind)
    | exact resolve eq67 eq27265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq27265
  have eq27341 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq27267
  have eq28779 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27341 eq101
    | exact resolve eq101 eq27341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq27341
  have eq28795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq28779
  have eq28798 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq28795
       have r₂ := eq28
       grind)
    | exact resolve eq28795 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28795
  have eq28802 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28798 eq74
    | exact resolve eq74 eq28798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq28798
  have eq28899 : y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq30 eq28802
    | exact resolve eq28802 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28802
  have eq28900 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq28899
  have eq28957 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66
       have i₂ := eq28900
       grind)
    | exact superpose eq28900 eq66
    | (have r₁ := eq66
       have r₂ := eq28900
       grind)
    | exact resolve eq66 eq28900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq28958 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq28900
       grind)
    | exact superpose eq28900 eq75
    | exact resolve eq75 eq28900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq28978 : y = (M.op x x) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq585 x
       have i₂ := eq28900
       grind)
    | exact superpose eq28900 eq585
    | exact resolve eq585 eq28900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28993 : y = (M.op x x) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq2927 x
       have i₂ := eq28900
       grind)
    | exact superpose eq28900 eq2927
    | exact resolve eq2927 eq28900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927 eq28900
  have eq29032 : (M.op x y) = (k x y) ∨ y = (M.op x x) := by grind
  clear eq28957
  have eq29049 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq28958
    | exact resolve eq28958 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28958
  have eq29080 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq585 x
       have i₂ := eq28978
       grind)
    | exact superpose eq28978 eq585
    | exact resolve eq585 eq28978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28978
  have eq29139 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29080
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29080
    | exact resolve eq29080 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29080
  have eq29447 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq592 x
       have i₂ := eq28993
       grind)
    | exact superpose eq28993 eq592
    | exact resolve eq592 eq28993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28993
  have eq29504 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq29447
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq29447
    | exact resolve eq29447 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29447
  have eq29522 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq29504
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29504
    | exact resolve eq29504 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29504
  have eq29527 : x = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq29522
    | exact resolve eq29522 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29522
  have eq29724 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29527 eq46
    | exact resolve eq46 eq29527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq29527
  have eq29756 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29724
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29724
    | exact resolve eq29724 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29724
  have eq30007 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq29032
       grind)
    | exact superpose eq29032 eq45
    | exact resolve eq45 eq29032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq29032
  have eq30041 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq30007
    | exact resolve eq30007 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30007
  have eq31153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30041 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq30041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30041
  have eq31163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq31153
    | exact resolve eq31153 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31153
  have eq31174 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq31163
       have r₂ := eq28
       grind)
    | exact resolve eq31163 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31163
  have eq31178 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq31174
    | exact resolve eq31174 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31174
  have eq89989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29049 eq31178
    | exact resolve eq31178 eq29049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29049 eq31178
  have eq90136 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq89989
  have eq90148 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq90136
       have r₂ := eq28
       grind)
    | exact resolve eq90136 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90136
  have eq90200 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq585 x
       have i₂ := eq90148
       grind)
    | exact superpose eq90148 eq585
    | exact resolve eq585 eq90148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq90202 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq592 x
       have i₂ := eq90148
       grind)
    | exact superpose eq90148 eq592
    | exact resolve eq592 eq90148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq90148
  have eq90274 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq90202
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq90202
    | exact resolve eq90202 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq90202
  have eq90275 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90200
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90200
    | exact resolve eq90200 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90200
  have eq90304 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq90274
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq90274
    | exact resolve eq90274 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90274
  have eq90311 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq90304
    | exact resolve eq90304 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90304
  have eq90314 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq90275 eq30
    | exact resolve eq30 eq90275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq90275
  have eq90531 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq90314
    | exact resolve eq90314 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq90314
  have eq90556 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq90311 eq28
    | exact resolve eq28 eq90311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90311
  have eq90773 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq90531 eq29139
    | exact resolve eq29139 eq90531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29139
  have eq90878 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq90531
  have eq90901 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90773
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90773
    | exact resolve eq90773 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq90773
  have eq90902 : x = (M.op x y) ∨ x = y := by grind
  clear eq90901
  have eq91470 : x = (M.op x y) := by
    first
    | (have r₁ := eq90902
       have r₂ := eq90878
       grind)
    | exact resolve eq90902 eq90878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90878 eq90902
  have eq91472 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq91470 eq21
    | exact resolve eq21 eq91470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq91470
  have eq91880 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq91472
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq91472
    | exact resolve eq91472 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq91472
  have eq91924 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq91880 eq27
    | exact resolve eq27 eq91880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq92075 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq91880 eq29756
    | exact resolve eq29756 eq91880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29756
  have eq92189 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq91880 eq90556
    | (have r₁ := eq90556
       have r₂ := eq91880
       grind)
    | exact resolve eq90556 eq91880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90556 eq91880
  have eq92190 : (σ (M.op x y)) = (σ y) := by grind
  clear eq92189
  have eq92271 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq92075
       have r₂ := eq28
       grind)
    | exact resolve eq92075 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92075
  have eq92412 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq92271
       have i₂ := eq69 sF1
       grind)
    | exact superpose eq69 eq92271
    | exact resolve eq92271 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq92271
  have eq94768 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq92190 eq91924
    | exact resolve eq91924 eq92190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91924 eq92190
  have eq94959 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq92412 eq94768
    | exact resolve eq94768 eq92412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92412 eq94768
  have eq94960 : False := by grind
  exact eq94960

/-- `Equation860`: `x = x ◇ ((y ◇ z) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation860 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law860 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law860.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) := by
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
  have eq72 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq106 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq670 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq107 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq671 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq670
    | exact resolve eq670 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq674 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq671
       have r₂ := eq27
       grind)
    | exact resolve eq671 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq676 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq674
    | exact resolve eq674 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq678 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq676
    | exact resolve eq676 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq680 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq678 eq72
    | (have r₁ := eq72
       have r₂ := eq678
       grind)
    | exact resolve eq72 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq678
  have eq686 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq680
  have eq776 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq686
       have r₂ := eq685
       grind)
    | exact resolve eq686 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq686
  have eq780 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq776 eq55
    | exact resolve eq55 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq788 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq780
    | exact resolve eq780 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq780
  have eq792 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq788
       have r₂ := eq71
       grind)
    | exact resolve eq788 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq864 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq792
       grind)
    | exact superpose eq792 eq44
    | exact resolve eq44 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq865 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq792
       grind)
    | exact superpose eq792 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq866 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq865
  have eq868 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq866
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq866
    | exact resolve eq866 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq869 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq868
  have eq870 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq864
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq864
    | exact resolve eq864 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq873 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq869
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq869
    | exact resolve eq869 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq877 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq873 eq51
    | (have r₁ := eq51
       have r₂ := eq873
       grind)
    | exact resolve eq51 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq880 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq877
  have eq886 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq870 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq887 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq886
  have eq891 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq887
    | exact resolve eq887 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq892 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq891
  have eq897 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq892
    | exact resolve eq892 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq899 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq897 eq27
    | exact resolve eq27 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq946 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq880 eq55
    | exact resolve eq55 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq957 : y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq946
    | exact resolve eq946 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq960 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq957
       have r₂ := eq50
       grind)
    | exact resolve eq957 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq966 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq960
       grind)
    | exact superpose eq960 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq967 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq966
  have eq969 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq967
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq967
    | exact resolve eq967 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq970 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq969
  have eq974 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq970
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq970
    | exact resolve eq970 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq970
  have eq976 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq974 eq20
    | exact resolve eq20 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq981 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq974 eq71
    | (have r₁ := eq71
       have r₂ := eq974
       grind)
    | exact resolve eq71 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq990 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq974
  have eq991 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq981
  have eq1001 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq976
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq976
    | exact resolve eq976 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq1070 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1001 eq899
    | (have r₁ := eq899
       have r₂ := eq1001
       grind)
    | exact resolve eq899 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq1001
  have eq1073 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1070
  have eq1074 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1073
  have eq1109 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1074 eq51
    | (have r₁ := eq51
       have r₂ := eq1074
       grind)
    | exact resolve eq51 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1074
  have eq1113 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1109
  have eq1221 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1113 eq55
    | exact resolve eq55 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1113
  have eq1236 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1221
    | exact resolve eq1221 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1221
  have eq1239 : y = (k x y) := by
    first
    | (have r₁ := eq1236
       have r₂ := eq50
       grind)
    | exact resolve eq1236 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1236
  have eq1265 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1239
       grind)
    | exact superpose eq1239 eq44
    | exact resolve eq44 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1270 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1265
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1265
    | exact resolve eq1265 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1265
  have eq1283 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1270 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1284 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1283
  have eq1286 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1284
    | exact resolve eq1284 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1289 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1286
    | exact resolve eq1286 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1286
  have eq1295 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1289 eq72
    | (have r₁ := eq72
       have r₂ := eq1289
       grind)
    | exact resolve eq72 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq1301 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1289
  have eq1302 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1295
  have eq1303 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1270 eq1302
    | exact resolve eq1302 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270 eq1302
  have eq1304 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1303
  have eq1367 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1304
       have r₂ := eq1301
       grind)
    | exact resolve eq1304 eq1301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301 eq1304
  have eq1371 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1367 eq27
    | exact resolve eq27 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1367
  have eq1866 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq991
       have r₂ := eq990
       grind)
    | exact resolve eq991 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1867 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1866
       have i₂ := eq1239
       grind)
    | exact superpose eq1239 eq1866
    | exact resolve eq1866 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239 eq1866
  have eq1868 : x = (M.op x y) := by
    first
    | (have r₁ := eq1867
       have r₂ := eq990
       grind)
    | exact resolve eq1867 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990 eq1867
  have eq1870 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1868 eq20
    | exact resolve eq20 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1868
  have eq1898 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1870
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1870
    | exact resolve eq1870 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1870
  have eq1901 : False := by grind
  exact eq1901

/-- `Equation882`: `x = y ◇ ((x ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation882 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law882 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law882.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq56 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq178 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq185 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X1
       have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq178 X0 X1
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq178 X1 X1
       have r₂ := eq59 X1 X1
       grind)
    | exact resolve eq178 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq178
  have eq471 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq185 (σ X1) (σ X0)
       grind)
    | exact superpose eq185 eq15
    | exact resolve eq15 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq471 X0 X1
       have i₂ := eq185 X1 X0
       grind)
    | exact superpose eq185 eq471
    | exact resolve eq471 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq471
  have eq481 : False := by grind
  exact eq481
