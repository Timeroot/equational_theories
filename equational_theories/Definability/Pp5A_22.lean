import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_x_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
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
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq81 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq82 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq14 (τ X1) (τ X0)
       grind)
    | exact superpose eq14 eq43
    | (have j1 := eq14 (τ X0) (τ X0)
       grind)
    | exact resolve eq43 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq79 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq79 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 : G, (M.op (M.op (σ (k X0 X0)) (σ X0)) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) X1
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq19
    | (have j1 := eq79 X0 X0
       grind)
    | exact resolve eq19 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq261 : ∀ X0 X1 : G, (M.op (M.op (σ (k X0 X0)) (σ X0)) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq257 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq262 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq256 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq265 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq262 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq262 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq262 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq297 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) ∨ (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq265 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq33 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq33 eq265
    | (have j0 := eq265 (M.op (M.op X0 X0) X0) X1
       grind)
    | exact resolve eq265 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq306 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq297 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq297 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq19 eq297
    | (have j0 := eq297 X0 X1
       grind)
    | exact resolve eq297 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq307 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq306 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq480 : ∀ X0 X1 : G, (M.op (M.op (σ (k (τ X0) (τ X0))) X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq261 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq261
    | exact resolve eq261 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq504 : ∀ X0 X1 : G, (M.op (M.op (k (σ (τ X0)) X0) X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq480 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq480
    | (have j0 := eq480 X0 X1
       grind)
    | exact resolve eq480 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq480
  have eq508 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq504 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq504
    | (have j0 := eq504 X0 X1
       grind)
    | exact resolve eq504 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq517 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (M.op (τ (k X0 X0)) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq508 (τ X0) X1
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq508
    | (have j0 := eq508 (τ X0) X1
       grind)
    | exact resolve eq508 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq569 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81
    | (have j0 := eq81 X1 X1
       grind)
    | exact resolve eq81 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq603 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq569 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq569
    | (have j0 := eq569 X0 X1
       grind)
    | exact resolve eq569 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq651 : ∀ X0 X1 : G, (k (τ X0) (M.op (M.op X1 X1) X1)) = (τ (M.op X0 (σ (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq307 X1 X0
       grind)
    | exact superpose eq307 eq30
    | exact resolve eq30 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq692 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (M.op X1 X1) X1)) = (τ (M.op X0 (σ (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq651 X0 X1
       have i₂ := eq33 X1 (τ X0)
       grind)
    | exact superpose eq33 eq651
    | exact resolve eq651 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq651
  have eq1184 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq250
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq250
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq250 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq1185 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1184
  have eq4044 : ∀ X0 X1 : G, (τ (σ (M.op (M.op X0 X0) X0))) = (M.op (τ (M.op (M.op X1 X1) X1)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq692 (M.op (M.op X1 X1) X1) X0
       have i₂ := eq19 X1 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq19 eq692
    | exact resolve eq692 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq4107 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (τ (M.op (M.op X1 X1) X1)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4044 X0 X1
       have i₂ := eq10 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq10 eq4044
    | exact resolve eq4044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4044
  have eq4560 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) (τ (M.op (M.op X0 X0) X0))) (τ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ (M.op (M.op X0 X0) X0)) (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0)))
       have i₂ := eq4107 (τ (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq4107 eq9
    | exact resolve eq9 eq4107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4107
  have eq4599 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4560 X0 X1
       have i₂ := eq19 (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))
       grind)
    | (have i₁ := eq4560 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) (τ (M.op (M.op X0 X0) X0))) (τ (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq19 eq4560
    | exact resolve eq4560 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4560
  have eq15978 : ∀ X0 X1 X2 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op (M.op (τ (k X0 X0)) (τ X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq517 X0 X2
       grind)
    | exact superpose eq517 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq517 X0 X2
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq517 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op (τ (k X0 X0)) (τ X0))
       have r₂ := eq517 X0 (M.op (τ (k X0 X0)) (τ X0))
       grind)
    | exact resolve eq12 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq16038 : ∀ X0 X1 X2 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op (M.op (τ (k X0 X0)) (τ X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq15978 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15978
  have eq31327 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1185
       grind)
    | exact superpose eq1185 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1185
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1185
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1185
       grind)
    | exact resolve eq13 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq31354 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31327
  have eq31355 : y = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31354
  have eq35094 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op (M.op (τ (k X1 X1)) (τ X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 X1 X0
       have i₂ := eq16038 X1 (τ X0) X2
       grind)
    | exact superpose eq16038 eq43
    | (have j1 := eq16038 X1 X1 X2
       grind)
    | exact resolve eq43 eq16038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq16038
  have eq65751 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (k X0 X0)) (τ X0)) X1) = X1 ∨ (M.op (M.op (τ (k X0 X0)) (τ X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (τ X0) X1
       have i₂ := eq35094 X0 X0 X2
       grind)
    | exact superpose eq35094 eq19
    | (have j1 := eq35094 X0 X0 X1
       grind)
    | exact resolve eq19 eq35094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq35094
  have eq139911 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (M.op (M.op (τ (k X0 X0)) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq65751 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65751
  have eq139912 : ∀ X0 X1 : G, (M.op (M.op (τ (k X0 X0)) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq139911 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139911
  have eq140079 : ∀ X0 X1 : G, (M.op (M.op (k X0 (τ (σ X0))) (τ (σ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq139912 (σ X0) X1
       have i₂ := eq40 X0 (σ X0)
       grind)
    | exact superpose eq40 eq139912
    | exact resolve eq139912 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq139912
  have eq140516 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq140079 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq140079
    | exact resolve eq140079 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140079
  have eq141106 : ∀ X0 X1 : G, (M.op (M.op (σ (k X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq140516 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq140516
    | exact resolve eq140516 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141211 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op (k X0 X0) X0) (M.op (k X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4599 (M.op (k X0 X0) X0) X1
       have i₂ := eq140516 X0 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq140516 eq4599
    | exact resolve eq4599 eq140516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4599
  have eq141476 : ∀ X0 X1 : G, (M.op (τ (M.op (k X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141211 X0 X1
       have i₂ := eq140516 X0 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq140516 eq141211
    | exact resolve eq141211 eq140516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140516 eq141211
  have eq141575 : ∀ X0 X1 : G, (M.op (τ (M.op (σ (k X0 X0)) (σ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141476 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq141476
    | exact resolve eq141476 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141476
  have eq650866 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq82 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq650868 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq650866 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650866
  have eq650923 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq650868 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq650868
    | exact resolve eq650868 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650868
  have eq651230 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq650923 X0
       have i₂ := eq30 (σ X0) X0
       grind)
    | exact superpose eq30 eq650923
    | (have j0 := eq650923 X0
       grind)
    | exact resolve eq650923 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq650923
  have eq651251 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq651230 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq651230
    | (have j0 := eq651230 X0
       grind)
    | exact resolve eq651230 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651230
  have eq651267 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq651251 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq651251 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq651251 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651251
  have eq651410 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141106 X0 X1
       have i₂ := eq651267 X0
       grind)
    | exact superpose eq651267 eq141106
    | exact resolve eq141106 eq651267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141106
  have eq651475 : ∀ X0 X1 : G, (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141575 X0 X1
       have i₂ := eq651267 X0
       grind)
    | exact superpose eq651267 eq141575
    | exact resolve eq141575 eq651267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141575
  have eq651586 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq258 X0 X0
       have i₂ := eq651267 X0
       grind)
    | exact superpose eq651267 eq258
    | (have j0 := eq258 X0 X0
       grind)
    | exact resolve eq258 eq651267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651697 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq651267 (σ X0)
       grind)
    | exact superpose eq651267 eq15
    | exact resolve eq15 eq651267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651823 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq651586 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651586
  have eq651924 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq651697 X0
       have i₂ := eq651267 X0
       grind)
    | exact superpose eq651267 eq651697
    | exact resolve eq651697 eq651267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651267 eq651697
  have eq656258 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq258 x y
       have i₂ := eq31355
       grind)
    | exact superpose eq31355 eq258
    | (have j0 := eq258 x y
       grind)
    | exact resolve eq258 eq31355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq31355
  have eq656295 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq656258
  have eq656296 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq656295
  have eq656305 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq656296
       have i₂ := eq651924 x
       grind)
    | exact superpose eq651924 eq656296
    | exact resolve eq656296 eq651924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656296
  have eq1433392 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq656305
       grind)
    | exact superpose eq656305 eq16
    | exact resolve eq16 eq656305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1433396 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq656305
       grind)
    | exact superpose eq656305 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq656305
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq656305
       grind)
    | exact resolve eq13 eq656305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656305
  have eq1433472 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq1433396
  have eq1433474 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq651823 x
       grind)
    | (have r₁ := eq1433472
       have r₂ := eq651823 x
       grind)
    | exact resolve eq1433472 eq651823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433472
  have eq1433475 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1433474
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1433474
    | exact resolve eq1433474 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433474
  have eq1433476 : x = (M.op x x) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1433475
       have i₂ := eq651924 x
       grind)
    | exact superpose eq651924 eq1433475
    | exact resolve eq1433475 eq651924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433475
  have eq1435871 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq651823 x
       have i₂ := eq1433476
       grind)
    | exact superpose eq1433476 eq651823
    | (have j0 := eq651823 x
       grind)
    | (have r₁ := eq651823 x
       have r₂ := eq1433476
       grind)
    | exact resolve eq651823 eq1433476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433476
  have eq1435980 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq1435871
  have eq1435986 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have j1 := eq651823 x
       grind)
    | (have r₁ := eq1435980
       have r₂ := eq651823 x
       grind)
    | exact resolve eq1435980 eq651823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435980
  have eq1436089 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1435986
       have i₂ := eq651924 x
       grind)
    | exact superpose eq651924 eq1435986
    | exact resolve eq1435986 eq651924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435986
  have eq1436174 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq603 y x
       have i₂ := eq1436089
       grind)
    | exact superpose eq1436089 eq603
    | (have j0 := eq603 y x
       grind)
    | exact resolve eq603 eq1436089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq1436089
  have eq1436962 : y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1436174
       have r₂ := eq1433392
       grind)
    | exact resolve eq1436174 eq1433392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436174
  have eq1445463 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1433392
       have i₂ := eq1436962
       grind)
    | exact superpose eq1436962 eq1433392
    | exact resolve eq1433392 eq1436962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433392 eq1436962
  have eq1445543 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq1445463
  have eq1445544 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq1445543
  have eq1447945 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq651823 x
       have i₂ := eq1445544
       grind)
    | exact superpose eq1445544 eq651823
    | (have j0 := eq651823 x
       grind)
    | (have r₁ := eq651823 x
       have r₂ := eq1445544
       grind)
    | exact resolve eq651823 eq1445544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445544
  have eq1448054 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq1447945
  have eq1448060 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq651823 x
       grind)
    | (have r₁ := eq1448054
       have r₂ := eq651823 x
       grind)
    | exact resolve eq1448054 eq651823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651823 eq1448054
  have eq1448163 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1448060
       have i₂ := eq651924 x
       grind)
    | exact superpose eq651924 eq1448060
    | exact resolve eq1448060 eq651924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448060
  have eq1448263 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq651410 x X0
       have i₂ := eq1448163
       grind)
    | exact superpose eq1448163 eq651410
    | exact resolve eq651410 eq1448163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651410
  have eq1448264 : ∀ X0 : G, (M.op (τ (M.op (σ x) (σ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq651475 x X0
       have i₂ := eq1448163
       grind)
    | exact superpose eq1448163 eq651475
    | exact resolve eq651475 eq1448163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651475
  have eq1448327 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1448163
       grind)
    | exact superpose eq1448163 eq10
    | exact resolve eq10 eq1448163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1449104 : x = (M.op x x) := by
    first
    | (have i₁ := eq1448327
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1448327
    | exact resolve eq1448327 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448327
  have eq1449151 : ∀ X0 : G, (M.op (τ (σ (M.op x x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1448264 X0
       have i₂ := eq651924 x
       grind)
    | exact superpose eq651924 eq1448264
    | exact resolve eq1448264 eq651924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448264
  have eq1449152 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1448263 X0
       have i₂ := eq651924 x
       grind)
    | exact superpose eq651924 eq1448263
    | exact resolve eq1448263 eq651924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651924 eq1448263
  have eq1449299 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1449151 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq1449151
    | exact resolve eq1449151 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449151
  have eq1449300 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1449152 X0
       have i₂ := eq1448163
       grind)
    | exact superpose eq1448163 eq1449152
    | exact resolve eq1449152 eq1448163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448163 eq1449152
  have eq1449392 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1449299 X0
       have i₂ := eq1449104
       grind)
    | exact superpose eq1449104 eq1449299
    | exact resolve eq1449299 eq1449104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449104 eq1449299
  have eq1456178 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1449300 (σ y)
       grind)
    | exact superpose eq1449300 eq16
    | exact resolve eq16 eq1449300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449300
  have eq1457225 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1456178
       have i₂ := eq1449392 y
       grind)
    | exact superpose eq1449392 eq1456178
    | exact resolve eq1456178 eq1449392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449392 eq1456178
  have eq1457226 : False := by grind
  exact eq1457226

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_pyy_pyx_pyy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq66 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq69 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq66 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq66 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq66 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq68 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq68 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq68 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq141 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq69 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq69
    | (have j0 := eq69 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq69 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq69 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq69 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq148 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq151 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq148 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq148 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq148 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq153 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq151
    | (have j0 := eq151 X0 X1
       grind)
    | exact resolve eq151 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq151
  have eq178 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq72 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq182 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X1
       have j1 := eq153 X1 X0
       grind)
    | (have r₁ := eq178 X1 X0
       have r₂ := eq153 X0 X1
       grind)
    | (have r₁ := eq178 X1 X1
       have r₂ := eq153 X1 X1
       grind)
    | exact resolve eq178 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq178
  have eq621 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq182 (σ X1) (σ X0)
       grind)
    | exact superpose eq182 eq15
    | exact resolve eq15 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq621 X0 X1
       have i₂ := eq182 X1 X0
       grind)
    | exact superpose eq182 eq621
    | exact resolve eq621 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq621
  have eq632 : False := by grind
  exact eq632

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq50
    | exact resolve eq50 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq70
  have eq97 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq97
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq113
    | exact resolve eq113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq13920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq13920
    | exact resolve eq13920 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13920
  have eq13932 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq13921
       have r₂ := eq28
       grind)
    | exact resolve eq13921 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13921
  have eq13936 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq13932
    | exact resolve eq13932 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13932
  have eq13938 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq13936 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13936
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq13936
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq13936
       grind)
    | exact resolve eq13 eq13936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13936
  have eq13956 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq13938
       have r₂ := eq27
       grind)
    | exact resolve eq13938 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13938
  have eq14161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq13956 eq114
    | exact resolve eq114 eq13956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq13956
  have eq14170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14161
  have eq14173 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14170
       have r₂ := eq28
       grind)
    | exact resolve eq14170 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14170
  have eq14175 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq14173
       grind)
    | exact superpose eq14173 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq14173
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq14173
       grind)
    | exact resolve eq13 eq14173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14173
  have eq14193 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14175
       have r₂ := eq19
       grind)
    | exact resolve eq14175 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14175
  have eq14511 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq14193
       grind)
    | exact superpose eq14193 eq97
    | exact resolve eq97 eq14193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq14193
  have eq14527 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq14511
    | exact resolve eq14511 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14511
  have eq14883 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14527 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq14527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq14883
  have eq14888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq14884
    | exact resolve eq14884 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14884
  have eq14899 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq14888
       have r₂ := eq28
       grind)
    | exact resolve eq14888 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14888
  have eq14903 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq14899
    | exact resolve eq14899 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14899
  have eq14931 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14903 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq14903
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq14903
       grind)
    | exact resolve eq13 eq14903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14903
  have eq14949 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq14931
       have r₂ := eq27
       grind)
    | exact resolve eq14931 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14931
  have eq15238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14949 eq14527
    | exact resolve eq14527 eq14949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14527 eq14949
  have eq15241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq15238
  have eq15246 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq15241
       have r₂ := eq28
       grind)
    | exact resolve eq15241 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15241
  have eq15249 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq15246 eq30
    | exact resolve eq30 eq15246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq15246
  have eq15366 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq15249
    | exact resolve eq15249 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15249
  have eq15367 : x = y := by grind
  clear eq15366
  have eq15662 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15367
       grind)
    | exact superpose eq15367 eq19
    | exact resolve eq19 eq15367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq15663 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq15367
       grind)
    | exact superpose eq15367 eq25
    | exact resolve eq25 eq15367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15367
  have eq15777 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15663
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15663
    | exact resolve eq15663 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15663
  have eq15792 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15777 eq27
    | exact resolve eq27 eq15777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15777
  have eq16786 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15792 eq71
    | exact resolve eq71 eq15792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq15792
  have eq16846 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16786
       have i₂ := eq15662
       grind)
    | exact superpose eq15662 eq16786
    | exact resolve eq16786 eq15662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15662 eq16786
  have eq16859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16846 eq15
    | exact resolve eq15 eq16846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16846
  have eq16903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16859
    | exact resolve eq16859 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16859
  have eq16912 : False := by grind
  exact eq16912

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_y_pyx_y_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
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
  have eq77 : x ≠ (M.op x y) ∨ (M.op x x) = (M.op y x) ∨ x = (k y x) := by
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
  have eq78 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq92 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq86 y x
       grind)
    | exact superpose eq86 eq92
    | (have j1 := eq86 y x
       grind)
    | exact resolve eq92 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq126 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq124
    | exact resolve eq124 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq127 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq126
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq126
    | exact resolve eq126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq86
    | (have j0 := eq86 (σ y) (σ x)
       grind)
    | exact resolve eq86 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq196
    | exact resolve eq196 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq200 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq197
       have r₂ := eq27
       grind)
    | exact resolve eq197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq202 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq200
    | exact resolve eq200 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq204 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq202 eq27
    | exact resolve eq27 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1197 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq202 eq78
    | (have r₁ := eq78
       have r₂ := eq202
       grind)
    | exact resolve eq78 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq202
  have eq1198 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1197
  have eq1207 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1198 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1198
       grind)
    | exact resolve eq13 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1209 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1207
  have eq1215 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1209
    | exact resolve eq1209 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq1215
    | exact resolve eq1215 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq1215
  have eq1225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1217
  have eq1228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1225
       have r₂ := eq204
       grind)
    | exact resolve eq1225 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq1225
  have eq1229 : x = (M.op x y) := by
    first
    | (have r₁ := eq1228
       have r₂ := eq27
       grind)
    | exact resolve eq1228 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1230 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1229 eq20
    | exact resolve eq20 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1233 : x ≠ x ∨ (M.op x x) = (M.op y x) ∨ x = (k y x) := by
    first
    | exact superpose eq1229 eq77
    | (have r₁ := eq77
       have r₂ := eq1229
       grind)
    | exact resolve eq77 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1238 : (M.op x x) = (M.op y x) ∨ x = (k y x) := by grind
  clear eq1233
  have eq1244 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1230
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1230
    | exact resolve eq1230 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1325 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1244 eq26
    | exact resolve eq26 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1655 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1238
       grind)
    | exact superpose eq1238 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1238
       grind)
    | exact resolve eq13 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1661 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq1655
  have eq1662 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq1661
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1661
    | exact resolve eq1661 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1661
  have eq1664 : x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq1229 eq1662
    | exact resolve eq1662 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229 eq1662
  have eq1665 : x = (k y x) := by grind
  clear eq1664
  have eq1670 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq1665
       grind)
    | exact superpose eq1665 eq92
    | exact resolve eq92 eq1665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1665
  have eq1677 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1244 eq1670
    | exact resolve eq1670 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq1679 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1677
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1677
    | exact resolve eq1677 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1677
  have eq1680 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1244 eq1679
    | exact resolve eq1679 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244 eq1679
  have eq1683 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1680 eq86
    | (have j0 := eq86 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq86 eq1680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq1680
  have eq1684 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1683
  have eq1686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1325 eq1684
    | exact resolve eq1684 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325 eq1684
  have eq1689 : False := by grind
  exact eq1689

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_pyy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq14 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = (k (M.op (M.op X1 (M.op X2 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = (k (M.op (M.op X1 (M.op X2 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
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
  clear eq23
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
  clear eq37
  have eq93 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq93 y x
       grind)
    | exact superpose eq93 eq74
    | (have j1 := eq93 y x
       grind)
    | exact resolve eq74 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq116
    | exact resolve eq116 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq585 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op X0 X0) x x X3
       have i₂ := eq53 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq630 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq117 eq93
    | (have j0 := eq93 (σ y) (σ x)
       grind)
    | exact resolve eq93 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq630
    | exact resolve eq630 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq634 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq631
       have r₂ := eq28
       grind)
    | exact resolve eq631 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq701 : ∀ X0 : G, y = (M.op x x) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq634 eq585
    | exact resolve eq585 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq712 : ∀ X0 X1 : G, (M.op (σ y) X1) = X1 ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq585 x X0
       have i₂ := eq701 X1
       grind)
    | exact superpose eq701 eq585
    | (have j1 := eq701 X1
       grind)
    | exact resolve eq585 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq722 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq712 (M.op X0 X1) X1
       grind)
    | exact superpose eq712 eq13
    | (have j0 := eq13 (σ y) X0
       have j1 := eq712 X1 X1
       grind)
    | (have r₁ := eq13 (σ y) X1
       have r₂ := eq712 X0 X1
       grind)
    | (have r₁ := eq13 y X0
       have r₂ := eq712 X0 X1
       grind)
    | exact resolve eq13 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq731 : ∀ X0 X1 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq722 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq777 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X1) X0))) = (k (M.op X0 (M.op (M.op X1 X1) X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X1))
       have i₂ := eq53 X0 X1 (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X1))
       grind)
    | exact superpose eq53 eq67
    | exact resolve eq67 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq67
  have eq780 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq777 x X0 X2
       have i₂ := eq585 X0 x
       grind)
    | (have i₁ := eq777 X0 x X2
       have i₂ := eq585 X0 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq585 eq777
    | exact resolve eq777 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq842 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq117
       have i₂ := eq731 X0 (k sF3 sF2)
       grind)
    | exact superpose eq731 eq117
    | (have j1 := eq731 X0 X0
       grind)
    | exact resolve eq117 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq731
  have eq846 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq842
    | (have j0 := eq842 X0
       grind)
    | exact resolve eq842 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq849 : ∀ X0 : G, y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq846 X0
       grind)
    | (have r₁ := eq846 X0
       have r₂ := eq28
       grind)
    | exact resolve eq846 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq856 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq585 x X1
       have i₂ := eq849 X0
       grind)
    | exact superpose eq849 eq585
    | (have j1 := eq849 X1
       grind)
    | exact resolve eq585 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585 eq849
  have eq898 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq856 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq899 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq898 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq919 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq780 y x
       have i₂ := eq899 y
       grind)
    | exact superpose eq899 eq780
    | exact resolve eq780 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq961 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq919 x
       grind)
    | exact superpose eq919 eq74
    | exact resolve eq74 eq919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq962 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq919 y
       grind)
    | exact superpose eq919 eq75
    | exact resolve eq75 eq919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq919
  have eq964 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq962
       have i₂ := eq899 y
       grind)
    | exact superpose eq899 eq962
    | exact resolve eq962 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq962
  have eq965 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq961
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq961
    | exact resolve eq961 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq961
  have eq967 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq964
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq964
    | exact resolve eq964 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq964
  have eq968 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq965
    | exact resolve eq965 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq965
  have eq973 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq967 eq93
    | (have j0 := eq93 (σ y) (σ y)
       grind)
    | exact resolve eq93 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq967
  have eq974 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq973
  have eq995 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq974 eq780
    | exact resolve eq780 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq974
  have eq1110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq995 eq968
    | exact resolve eq968 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968 eq995
  have eq1118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq1110
    | exact resolve eq1110 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1110
  have eq1128 : False := by grind
  exact eq1128

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq206 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq44 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq209 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq206 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq206 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq206 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq206 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq206 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq1290 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq209
  have eq1308 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1290 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1686 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1308 (σ X1) (σ X0)
       grind)
    | exact superpose eq1308 eq15
    | exact resolve eq15 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1697 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1686 X0 X1
       have i₂ := eq1308 X1 X0
       grind)
    | exact superpose eq1308 eq1686
    | exact resolve eq1686 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308 eq1686
  have eq1707 : False := by grind
  exact eq1707

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_y_pyx_pxy_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  clear eq35
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
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq16 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq16 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq389 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq174 (τ X0)
       grind)
    | exact superpose eq174 eq38
    | exact resolve eq38 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq389 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq389
    | exact resolve eq389 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq441 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq339 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq339
    | exact resolve eq339 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq339
  have eq463 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq441 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq441
    | exact resolve eq441 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq691 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq176 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq176 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq176 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq176 x (M.op X0 X0) X0
       have i₂ := eq691 (M.op X0 X0) x X2
       grind)
    | (have i₁ := eq176 (M.op X2 X2) (M.op X2 X2) X2
       have i₂ := eq691 X0 x (M.op (M.op X2 X2) (M.op X2 X2))
       grind)
    | exact superpose eq691 eq176
    | exact resolve eq176 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq691
  have eq768 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq724 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq724 X1 X0
       grind)
    | exact superpose eq724 eq13
    | (have j0 := eq13 X2 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X2
       have r₂ := eq724 X0 X2
       grind)
    | (have r₁ := eq13 (M.op X2 X2) X0
       have r₂ := eq724 X0 X2
       grind)
    | exact resolve eq13 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq463 X1
       have i₂ := eq724 X0 (σ X1)
       grind)
    | (have i₁ := eq463 X1
       have i₂ := eq724 (σ X1) X0
       grind)
    | exact superpose eq724 eq463
    | exact resolve eq463 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq782 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq421 X1
       have i₂ := eq724 X0 (τ X1)
       grind)
    | (have i₁ := eq421 X1
       have i₂ := eq724 (τ X1) X0
       grind)
    | exact superpose eq724 eq421
    | exact resolve eq421 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq850 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ (M.op X1 X1))
       have i₂ := eq782 X1 (τ X0)
       grind)
    | exact superpose eq782 eq38
    | exact resolve eq38 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq863 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq850 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq850
    | exact resolve eq850 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq897 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq898 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 x x
       have i₂ := eq724 X0 x
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq724 X0 x
       grind)
    | exact superpose eq724 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq724 X0 X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq724 x x
       grind)
    | exact resolve eq12 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 (M.op X2 X2)) X0)) ≠ X0 ∨ (M.op (M.op (M.op X1 (M.op X2 X2)) X0) (M.op (M.op X1 (M.op X2 X2)) X0)) = X1 ∨ (k X1 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op (M.op X1 (M.op X2 X2)) X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq12
    | (have j0 := eq12 X1 (M.op (M.op X1 (M.op X2 X2)) X0)
       grind)
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq928 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq920 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq1395 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq695 X0 X1 x
       grind)
    | exact superpose eq695 eq16
    | exact resolve eq16 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq1484 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op (M.op X1 X1) X0)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X1) X0) x
       have i₂ := eq696 X1 x X0
       grind)
    | exact superpose eq696 eq16
    | exact resolve eq16 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1919 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1395 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1395
    | (have j0 := eq1395 x X0 y
       grind)
    | exact resolve eq1395 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1920 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq26 eq1395
    | (have j0 := eq1395 (σ x) X0 (σ y)
       grind)
    | exact resolve eq1395 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1945 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1395 (M.op (M.op X1 X1) X0) x X2
       have i₂ := eq696 X1 x X0
       grind)
    | exact superpose eq696 eq1395
    | exact resolve eq1395 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq1395
  have eq2039 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op x (M.op (M.op X0 X0) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1919 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))
       have i₂ := eq175 (M.op (M.op X0 X0) (M.op X1 X1)) X0 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq175 eq1919
    | exact resolve eq1919 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq3564 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq724 X2 X1
       have i₂ := eq928 X2 X0
       grind)
    | exact superpose eq928 eq724
    | (have j1 := eq928 X1 X0
       grind)
    | exact resolve eq724 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq3571 : ∀ X0 X1 X2 : G, (k (τ (k X0 X0)) X2) = X2 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq781 X1 X2
       have i₂ := eq928 X1 X0
       grind)
    | exact superpose eq928 eq781
    | (have j1 := eq928 X1 X0
       grind)
    | exact resolve eq781 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3671 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq782 X1 (σ (M.op X1 X1))
       have i₂ := eq928 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq928 eq782
    | (have j1 := eq928 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq782 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq3673 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) ∨ (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq863 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq928 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact superpose eq928 eq863
    | (have j1 := eq928 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact resolve eq863 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq3676 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq781 X1 (τ (M.op X1 X1))
       have i₂ := eq928 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq928 eq781
    | (have j1 := eq928 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq781 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq3683 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq928 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq3688 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3676 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3676
  have eq3691 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3673 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3673
  have eq3693 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3671 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3671
  have eq3725 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq897
       grind)
    | exact superpose eq897 eq40
    | exact resolve eq40 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq3726 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3725
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3725
    | exact resolve eq3725 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3725
  have eq3728 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq3726
    | exact resolve eq3726 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3726
  have eq3735 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq3688 x X2
       have i₂ := eq3688 x X0
       grind)
    | exact superpose eq3688 eq3688
    | exact resolve eq3688 eq3688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3802 : ∀ X0 X2 X3 : G, (τ (M.op X0 X0)) ≠ X2 ∨ (k X2 X3) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq768 x X3 X2
       have i₂ := eq3688 x X0
       grind)
    | exact superpose eq3688 eq768
    | (have j0 := eq768 X0 X3 X2
       grind)
    | (have r₁ := eq768 X0 x (τ (M.op x x))
       have r₂ := eq3688 X0 x
       grind)
    | exact resolve eq768 eq3688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3688
  have eq4083 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (σ (M.op X0 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X1 x x X2
       have i₂ := eq3693 (M.op x x) X0
       grind)
    | exact superpose eq3693 eq175
    | exact resolve eq175 eq3693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq4097 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op X0 X0)) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1945 (M.op X1 X1) X1 X2
       have i₂ := eq3693 (M.op X1 X1) X0
       grind)
    | exact superpose eq3693 eq1945
    | exact resolve eq1945 eq3693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945
  have eq4099 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 (M.op X2 X2)) X1 X2
       have i₂ := eq3693 (M.op X1 (M.op X2 X2)) X0
       grind)
    | exact superpose eq3693 eq16
    | exact resolve eq16 eq3693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4529 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq1920 x
       have i₂ := eq3691 x X0
       grind)
    | exact superpose eq3691 eq1920
    | exact resolve eq1920 eq3691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920
  have eq4540 : ∀ X0 X2 : G, (σ (M.op X2 X2)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq3693 x X2
       have i₂ := eq3691 x X0
       grind)
    | exact superpose eq3691 eq3693
    | exact resolve eq3693 eq3691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3691 eq3693
  have eq76346 : ∀ X0 X1 : G, (k (k x x) X0) = X0 ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq97 eq3571
    | (have j0 := eq3571 (σ x) X1 x
       grind)
    | exact resolve eq3571 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq76537 : ∀ X0 X1 : G, (k x x) ≠ (k x x) ∨ (M.op X0 X0) = (k x x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq3683 X0 (k x x)
       have i₂ := eq76346 (k x x) X1
       grind)
    | exact superpose eq76346 eq3683
    | (have j0 := eq3683 X0 (k x x)
       have j1 := eq76346 X0 X1
       grind)
    | (have r₁ := eq3683 X0 (k x x)
       have r₂ := eq76346 (k x x) X1
       grind)
    | exact resolve eq3683 eq76346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76346
  have eq76568 : ∀ X0 X1 : G, (M.op X0 X0) = (k x x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq76537 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76537
  have eq76602 : ∀ X1 : G, (k x x) = (k (σ x) (σ x)) ∨ (M.op X1 X1) = (σ x) := by
    intro X1
    first
    | exact superpose eq3564 eq76568
    | (have j0 := eq76568 x X1
       have j1 := eq3564 (σ x) X1 X1
       grind)
    | exact resolve eq76568 eq3564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76568
  have eq78750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3728 eq898
    | exact resolve eq898 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78757 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq78750
       have r₂ := eq27
       grind)
    | exact resolve eq78750 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78750
  have eq78763 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k x x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3564 eq78757
    | (have j1 := eq3564 x x y
       grind)
    | exact resolve eq78757 eq3564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78757
  have eq78768 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k x x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq78763 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq78763
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq78763
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq78763
       grind)
    | exact resolve eq12 eq78763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78763
  have eq78784 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k x x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq78768
       have r₂ := eq26
       grind)
    | exact resolve eq78768 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78768
  have eq78794 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq76602 eq78784
    | (have j1 := eq76602 (σ y)
       grind)
    | exact resolve eq78784 eq76602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76602 eq78784
  have eq78800 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq3683 (σ y) (σ x)
       grind)
    | (have r₁ := eq78794
       have r₂ := eq3683 x (σ x)
       grind)
    | exact resolve eq78794 eq3683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78794
  have eq78804 : (σ x) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3564 eq78800
    | (have j1 := eq3564 x x y
       grind)
    | exact resolve eq78800 eq3564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3564 eq78800
  have eq78806 : (σ x) = (k x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3728 eq78804
    | exact resolve eq78804 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728 eq78804
  have eq78807 : (σ x) = (k x x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq78806
       have r₂ := eq27
       grind)
    | exact resolve eq78806 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78806
  have eq78834 : ∀ X0 X1 : G, (k (τ (σ x)) X0) = X0 ∨ (M.op X1 X1) = x ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq3571 x X1 X0
       have i₂ := eq78807
       grind)
    | exact superpose eq78807 eq3571
    | (have j0 := eq3571 x X1 x
       grind)
    | exact resolve eq3571 eq78807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3571 eq78807
  have eq78851 : ∀ X0 X1 : G, (k x X0) = X0 ∨ (M.op X1 X1) = x ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq29 eq78834
    | (have j0 := eq78834 X0 X1
       grind)
    | exact resolve eq78834 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78834
  have eq78877 : ∀ X0 X1 : G, (k x X0) = X0 ∨ (M.op X1 X1) = x ∨ (M.op x y) = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq78851 X0 X1
       have j1 := eq768 X0 X0 x
       grind)
    | (have r₁ := eq78851 (M.op X0 X0) X1
       have r₂ := eq768 X0 X1 (k x (M.op X0 X0))
       grind)
    | (have r₁ := eq78851 X0 X0
       have r₂ := eq768 X0 X1 x
       grind)
    | (have r₁ := eq78851 X0 X1
       have r₂ := eq768 y X1 x
       grind)
    | exact resolve eq78851 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78851
  have eq78884 : ∀ X0 : G, (M.op x y) = (M.op y x) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq78877 X0 x
       have j1 := eq768 X0 X0 x
       grind)
    | (have r₁ := eq78877 (M.op X0 X0) x
       have r₂ := eq768 X0 x (k x (M.op X0 X0))
       grind)
    | (have r₁ := eq78877 X0 X0
       have r₂ := eq768 X0 x x
       grind)
    | exact resolve eq78877 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78877
  have eq78898 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 x y
       have i₂ := eq78884 X0
       grind)
    | (have i₁ := eq12 X0 x
       have i₂ := eq78884 (M.op x X0)
       grind)
    | exact superpose eq78884 eq12
    | (have j0 := eq12 x y
       have j1 := eq78884 X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq78884 X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq78884 X0
       grind)
    | exact resolve eq12 eq78884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78884
  have eq78907 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq78898 X0
       have j1 := eq768 X0 X0 x
       grind)
    | (have r₁ := eq78898 X0
       have r₂ := eq768 y x x
       grind)
    | (have r₁ := eq78898 (M.op X0 X0)
       have r₂ := eq768 X0 x (k x (M.op X0 X0))
       grind)
    | exact resolve eq78898 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq78898
  have eq78910 : ∀ X0 : G, (M.op x y) = (k x y) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq78907 X0
       grind)
    | (have r₁ := eq78907 X0
       have r₂ := eq18
       grind)
    | exact resolve eq78907 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78907
  have eq78925 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40 x
       have i₂ := eq78910 X0
       grind)
    | (have i₁ := eq40 x
       have i₂ := eq78910 y
       grind)
    | exact superpose eq78910 eq40
    | (have j1 := eq78910 X0
       grind)
    | exact resolve eq40 eq78910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq78910
  have eq78927 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq78925 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78925
    | (have j0 := eq78925 X0
       grind)
    | exact resolve eq78925 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78925
  have eq78931 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq78927
    | (have j0 := eq78927 X0
       grind)
    | exact resolve eq78927 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78927
  have eq78936 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq898
       have i₂ := eq78931 (k sF2 sF3)
       grind)
    | exact superpose eq78931 eq898
    | (have j1 := eq78931 X0
       grind)
    | exact resolve eq898 eq78931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq78943 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq78936 X0
       grind)
    | (have r₁ := eq78936 X0
       have r₂ := eq27
       grind)
    | exact resolve eq78936 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78936
  have eq79886 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq78943 (M.op x X0)
       grind)
    | exact superpose eq78943 eq12
    | (have j0 := eq12 (σ x) (σ y)
       have j1 := eq78943 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq78943 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq78943 X0
       grind)
    | exact resolve eq12 eq78943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78943
  have eq79896 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq79886 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79886
  have eq79904 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq79896 X0
       grind)
    | (have r₁ := eq79896 X0
       have r₂ := eq26
       grind)
    | exact resolve eq79896 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79896
  have eq79911 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | exact superpose eq78931 eq79904
    | (have j0 := eq79904 X0
       have j1 := eq78931 X0
       grind)
    | exact resolve eq79904 eq78931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78931 eq79904
  have eq79915 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq79911 X0
       grind)
    | (have r₁ := eq79911 X0
       have r₂ := eq27
       grind)
    | exact resolve eq79911 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79911
  have eq80045 : ∀ X0 X1 : G, (τ (σ x)) = (τ (M.op X0 X0)) ∨ (k x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3735 X0 x
       have i₂ := eq79915 (M.op X0 X0)
       grind)
    | exact superpose eq79915 eq3735
    | (have j1 := eq79915 X1
       grind)
    | exact resolve eq3735 eq79915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3735 eq79915
  have eq80329 : ∀ X0 X1 : G, x = (τ (M.op X0 X0)) ∨ (k x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq29 eq80045
    | (have j0 := eq80045 X0 X1
       grind)
    | exact resolve eq80045 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80045
  have eq80456 : ∀ X1 : G, (k x X1) = X1 := by
    intro X1
    first
    | (have j0 := eq80329 x X1
       have j1 := eq3802 x x X1
       grind)
    | (have r₁ := eq80329 x X1
       have r₂ := eq3802 x x x
       grind)
    | (have r₁ := eq80329 x (τ (M.op x x))
       have r₂ := eq3802 x (k x (τ (M.op x x))) x
       grind)
    | exact resolve eq80329 eq3802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3802 eq80329
  have eq80557 : ∀ X0 : G, x ≠ x ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3683 X0 x
       have i₂ := eq80456 x
       grind)
    | exact superpose eq80456 eq3683
    | (have j0 := eq3683 X0 x
       grind)
    | (have r₁ := eq3683 X0 x
       have r₂ := eq80456 x
       grind)
    | exact resolve eq3683 eq80456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3683 eq80456
  have eq80588 : ∀ X0 : G, x = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq80557 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80557
  have eq80757 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 x) X2) X0) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq16 X2 X0 x
       have i₂ := eq80588 x
       grind)
    | exact superpose eq80588 eq16
    | exact resolve eq16 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80974 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4083 x X0 X1
       have i₂ := eq80588 x
       grind)
    | exact superpose eq80588 eq4083
    | exact resolve eq4083 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4083
  have eq80989 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4099 x X0 X1
       have i₂ := eq80588 x
       grind)
    | exact superpose eq80588 eq4099
    | exact resolve eq4099 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4099
  have eq81013 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (σ x)))) := by
    first
    | (have i₁ := eq4529 x
       have i₂ := eq80588 x
       grind)
    | exact superpose eq80588 eq4529
    | exact resolve eq4529 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4529
  have eq81020 : ∀ X1 : G, (σ x) = (σ (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq4540 X1 x
       have i₂ := eq80588 x
       grind)
    | exact superpose eq80588 eq4540
    | exact resolve eq4540 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4540
  have eq81118 : ∀ X0 X1 : G, (M.op x (M.op (M.op X1 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1484 X0 X1 X0
       have i₂ := eq80588 X0
       grind)
    | exact superpose eq80588 eq1484
    | exact resolve eq1484 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq81162 : y = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq2039 x x
       have i₂ := eq80588 (M.op x x)
       grind)
    | exact superpose eq80588 eq2039
    | exact resolve eq2039 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039
  have eq81185 : ∀ X0 : G, x = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4097 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq80588 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq80588 eq4097
    | exact resolve eq4097 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4097
  have eq81209 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 (M.op X1 X1)) X0 X1
       have i₂ := eq80588 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq80588 eq16
    | exact resolve eq16 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81269 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq81209 X0 x
       have i₂ := eq80588 x
       grind)
    | exact superpose eq80588 eq81209
    | exact resolve eq81209 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81209
  have eq81291 : x = (σ x) := by
    first
    | (have i₁ := eq81185 x
       have i₂ := eq80588 x
       grind)
    | exact superpose eq80588 eq81185
    | exact resolve eq81185 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81185
  have eq81307 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq81162
       have i₂ := eq80588 x
       grind)
    | exact superpose eq80588 eq81162
    | exact resolve eq81162 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81162
  have eq81343 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq81118 X0 x
       have i₂ := eq80588 x
       grind)
    | exact superpose eq80588 eq81118
    | exact resolve eq81118 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81118
  have eq81410 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq81020 x
       have i₂ := eq80588 x
       grind)
    | exact superpose eq80588 eq81020
    | exact resolve eq81020 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81020
  have eq81417 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (σ x)))) := by
    first
    | (have i₁ := eq81013
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq81013
    | exact resolve eq81013 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81013
  have eq81434 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq80989 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq80989
    | (have j0 := eq80989 X0 X1
       grind)
    | exact resolve eq80989 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80989
  have eq81449 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80974 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq80974
    | (have j0 := eq80974 X0 X1
       grind)
    | exact resolve eq80974 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80974
  have eq81697 : x = (σ x) := by
    first
    | (have i₁ := eq81291
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq81291
    | exact resolve eq81291 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81291
  have eq81784 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq81410
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq81410
    | exact resolve eq81410 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq81410
  have eq81800 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq81434 X0 x
       have i₂ := eq80588 x
       grind)
    | exact superpose eq80588 eq81434
    | exact resolve eq81434 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81434
  have eq82023 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq81800 X0
       have i₂ := eq81697
       grind)
    | exact superpose eq81697 eq81800
    | exact resolve eq81800 eq81697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81800
  have eq83768 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq81697
       grind)
    | exact superpose eq81697 eq18
    | exact resolve eq18 eq81697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109084 : ∀ X0 : G, (M.op (M.op y X0) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq81307 eq80757
    | exact resolve eq80757 eq81307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80757 eq81307
  have eq110527 : ∀ X0 : G, (M.op x y) ≠ (M.op y (M.op X0 X0)) ∨ y = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op x y) = (k y (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq109084 eq923
    | exact resolve eq923 eq109084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109084
  have eq110560 : ∀ X0 : G, (M.op x y) ≠ (M.op y x) ∨ y = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op x y) = (k y (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq110527 X0
       have i₂ := eq80588 X0
       grind)
    | exact superpose eq80588 eq110527
    | (have j0 := eq110527 X0
       grind)
    | exact resolve eq110527 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110527
  have eq110623 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ y = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op x y) = (k y (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq110560 X0
       have i₂ := eq81269 y
       grind)
    | exact superpose eq81269 eq110560
    | (have j0 := eq110560 X0
       grind)
    | (have r₁ := eq110560 X0
       have r₂ := eq81269 y
       grind)
    | exact resolve eq110560 eq81269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81269 eq110560
  have eq110665 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op x y) = (k y (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq110623 X0
       grind)
    | (have r₁ := eq110623 X0
       have r₂ := eq18
       grind)
    | exact resolve eq110623 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq110623
  have eq110686 : ∀ X0 : G, x = y ∨ (M.op x y) = (k y (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq110665 X0
       have i₂ := eq80588 (M.op X0 X0)
       grind)
    | exact superpose eq80588 eq110665
    | (have j0 := eq110665 X0
       grind)
    | exact resolve eq110665 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110665
  have eq110699 : ∀ X0 : G, y = (σ x) ∨ (M.op x y) = (k y (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq110686 X0
       have i₂ := eq81697
       grind)
    | exact superpose eq81697 eq110686
    | (have j0 := eq110686 X0
       grind)
    | exact resolve eq110686 eq81697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110686
  have eq110706 : (M.op x y) = (k y x) ∨ y = (σ x) := by
    first
    | (have i₁ := eq110699 x
       have i₂ := eq80588 x
       grind)
    | exact superpose eq80588 eq110699
    | exact resolve eq110699 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110699
  have eq110713 : (M.op x y) = (k y (σ x)) ∨ y = (σ x) := by
    first
    | (have i₁ := eq110706
       have i₂ := eq81697
       grind)
    | exact superpose eq81697 eq110706
    | exact resolve eq110706 eq81697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110706
  have eq111106 : (σ (M.op x y)) = (k (σ y) (σ (σ x))) ∨ y = (σ x) := by
    first
    | exact superpose eq110713 eq36
    | exact resolve eq36 eq110713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq110713
  have eq111109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (σ x) := by
    first
    | exact superpose eq81784 eq111106
    | exact resolve eq111106 eq81784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111106
  have eq111110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (σ x) := by
    first
    | exact superpose eq20 eq111109
    | exact resolve eq111109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111109
  have eq130619 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq81449
    | (have j0 := eq81449 (σ y) X0
       grind)
    | exact resolve eq81449 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81449
  have eq133308 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op X0 X0)) ∨ (σ y) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq130619 eq923
    | exact resolve eq923 eq130619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq130619
  have eq133349 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) x) ∨ (σ y) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq133308 X0
       have i₂ := eq80588 X0
       grind)
    | exact superpose eq80588 eq133308
    | (have j0 := eq133308 X0
       grind)
    | exact resolve eq133308 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133308
  have eq133414 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq133349 X0
       have i₂ := eq81697
       grind)
    | exact superpose eq81697 eq133349
    | (have j0 := eq133349 X0
       grind)
    | exact resolve eq133349 eq81697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133349
  have eq133465 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq82023 eq133414
    | (have j0 := eq133414 X0
       grind)
    | (have r₁ := eq133414 X0
       have r₂ := eq82023 (σ y)
       grind)
    | exact resolve eq133414 eq82023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82023 eq133414
  have eq133500 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq133465 X0
       grind)
    | (have r₁ := eq133465 X0
       have r₂ := eq26
       grind)
    | exact resolve eq133465 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133465
  have eq133518 : ∀ X0 : G, x = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq133500 X0
       have i₂ := eq80588 (M.op X0 X0)
       grind)
    | exact superpose eq80588 eq133500
    | (have j0 := eq133500 X0
       grind)
    | exact resolve eq133500 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133500
  have eq133529 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq133518 X0
       have i₂ := eq81697
       grind)
    | exact superpose eq81697 eq133518
    | (have j0 := eq133518 X0
       grind)
    | exact resolve eq133518 eq81697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133518
  have eq133537 : (M.op (σ x) (σ y)) = (k (σ y) x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq133529 x
       have i₂ := eq80588 x
       grind)
    | exact superpose eq80588 eq133529
    | exact resolve eq133529 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133529
  have eq133545 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq133537
       have i₂ := eq81697
       grind)
    | exact superpose eq81697 eq133537
    | exact resolve eq133537 eq81697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133537
  have eq134017 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq133545 eq111110
    | exact resolve eq111110 eq133545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111110 eq133545
  have eq134023 : (σ x) = (σ y) ∨ y = (σ x) := by
    first
    | (have r₁ := eq134017
       have r₂ := eq27
       grind)
    | exact resolve eq134017 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134017
  have eq134043 : y = (τ (σ x)) ∨ y = (σ x) := by
    first
    | exact superpose eq134023 eq31
    | exact resolve eq31 eq134023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq134023
  have eq134255 : x = y ∨ y = (σ x) := by
    first
    | exact superpose eq29 eq134043
    | exact resolve eq134043 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq134043
  have eq134326 : y = (σ x) ∨ y = (σ x) := by
    first
    | (have i₁ := eq134255
       have i₂ := eq81697
       grind)
    | exact superpose eq81697 eq134255
    | exact resolve eq134255 eq81697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134255
  have eq134327 : y = (σ x) := by grind
  clear eq134326
  have eq134381 : (σ y) = (σ (σ x)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq134327
       grind)
    | exact superpose eq134327 eq24
    | exact resolve eq24 eq134327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq134454 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq83768
       have i₂ := eq134327
       grind)
    | exact superpose eq134327 eq83768
    | exact resolve eq83768 eq134327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83768 eq134327
  have eq134459 : x = (M.op x y) := by
    first
    | (have i₁ := eq134454
       have i₂ := eq80588 sF2
       grind)
    | exact superpose eq80588 eq134454
    | exact resolve eq134454 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134454
  have eq134497 : (σ x) = (σ y) := by
    first
    | exact superpose eq81784 eq134381
    | exact resolve eq134381 eq81784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81784 eq134381
  have eq134688 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq81343 X0
       have i₂ := eq134459
       grind)
    | exact superpose eq134459 eq81343
    | exact resolve eq81343 eq134459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81343
  have eq134696 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq81697
       have i₂ := eq134459
       grind)
    | exact superpose eq134459 eq81697
    | exact resolve eq81697 eq134459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134459
  have eq134967 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq134497 eq26
    | exact resolve eq26 eq134497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq135141 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq134967
       have i₂ := eq80588 sF2
       grind)
    | exact superpose eq80588 eq134967
    | exact resolve eq134967 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80588 eq134967
  have eq135197 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq135141
       have i₂ := eq81697
       grind)
    | exact superpose eq81697 eq135141
    | exact resolve eq135141 eq81697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81697 eq135141
  have eq135248 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq134696 eq135197
    | exact resolve eq135197 eq134696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135197
  have eq135473 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (σ (M.op x y)))) := by
    first
    | exact superpose eq134696 eq81417
    | exact resolve eq81417 eq134696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81417
  have eq135510 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq135473
    | exact resolve eq135473 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq135473
  have eq135612 : (σ y) = (M.op (M.op x y) (M.op (M.op x y) (σ (M.op x y)))) := by
    first
    | exact superpose eq135248 eq135510
    | exact resolve eq135510 eq135248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135510
  have eq135702 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq134688 eq135612
    | exact resolve eq135612 eq134688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134688 eq135612
  have eq135778 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq134497 eq135702
    | exact resolve eq135702 eq134497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134497 eq135702
  have eq135844 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq134696 eq135778
    | exact resolve eq135778 eq134696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134696 eq135778
  have eq136210 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq135248 eq27
    | exact resolve eq27 eq135248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq135248
  have eq136305 : False := by grind
  exact eq136305

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxy_pyx_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq22
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq62 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X2 X2)) (M.op X1 X1) X1
       have i₂ := eq62 (M.op X1 X1) X0 X2
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq62 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (M.op X0 X0) x X1
       have i₂ := eq62 x (M.op X0 X0) X0
       grind)
    | exact superpose eq62 eq66
    | exact resolve eq66 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X0)
       have i₂ := eq68 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq12 X2 (M.op X0 X0)
       have i₂ := eq68 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X2 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq258 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq257 X0 x X2
       grind)
    | (have r₁ := eq257 x X0 X2
       have r₂ := eq66 X0 x x
       grind)
    | (have r₁ := eq257 (M.op X0 X0) (M.op X0 X0) X2
       have r₂ := eq66 X0 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq257 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq257
  have eq306 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op (M.op X2 X2) X0) x
       have i₂ := eq70 X2 x X0
       grind)
    | exact superpose eq70 eq62
    | exact resolve eq62 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq307 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op (M.op X1 X1) X0)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X1) X0) x
       have i₂ := eq70 X1 x X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = (τ (M.op (M.op X0 X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (M.op X0 X0)
       have i₂ := eq258 X0 (σ X1)
       grind)
    | exact superpose eq258 eq28
    | exact resolve eq28 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq529 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq964 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq529 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq529
    | (have j0 := eq529 X0 (σ X1)
       grind)
    | exact resolve eq529 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1000 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1) = (M.op X0 (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq61 (M.op X1 X0) X4 X5 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1)
       have i₂ := eq61 X1 X2 X3 X0
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1113 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) X3) X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))
       have i₂ := eq61 (M.op (M.op X0 X0) (M.op X1 X1)) X0 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1194 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X0) (σ X1))) = (k X1 (τ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq527 X2 X1
       have i₂ := eq306 (σ X1) X2 X0
       grind)
    | (have i₁ := eq527 X2 X1
       have i₂ := eq306 (σ X1) X0 X2
       grind)
    | exact superpose eq306 eq527
    | exact resolve eq527 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq1259 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X1 X1) X0)) = (k (τ X0) (τ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1194 X1 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1194
    | exact resolve eq1194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1268 : ∀ X0 X1 X3 : G, (k X0 (τ (M.op X1 X1))) = (k X0 (τ (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1194 x X0 X3
       have i₂ := eq1194 x X0 X1
       grind)
    | exact superpose eq1194 eq1194
    | exact resolve eq1194 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1310 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X1 X1) X0)) = (τ (k X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1259 X0 X1 X2
       have i₂ := eq31 (M.op X2 X2) X0
       grind)
    | exact superpose eq31 eq1259
    | exact resolve eq1259 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1317 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X1 X1) X0)) = (τ (M.op (M.op X2 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1310 X0 X1 X2
       have i₂ := eq258 X2 X0
       grind)
    | exact superpose eq258 eq1310
    | exact resolve eq1310 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq1844 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq964 x y
       grind)
    | exact superpose eq964 eq16
    | (have j1 := eq964 x y
       grind)
    | exact resolve eq16 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1846 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq964 X0 X0
       grind)
    | exact superpose eq964 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq964 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq964 X0 X1
       grind)
    | exact resolve eq12 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1893 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1846 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq1846 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq1846 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846
  have eq2010 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (τ (M.op (M.op X2 X2) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1317 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq70 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq70 eq1317
    | exact resolve eq1317 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1317
  have eq4320 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1893 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1893
    | (have j0 := eq1893 (τ X0) X1
       grind)
    | exact resolve eq1893 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1893
  have eq4321 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4320 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4320
    | (have j0 := eq4320 X0 X1
       grind)
    | exact resolve eq4320 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4320
  have eq4331 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4321 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4321
    | (have j0 := eq4321 X0 X1
       grind)
    | exact resolve eq4321 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4321
  have eq4360 : ∀ X0 X1 X2 : G, (τ (M.op X1 X1)) ≠ (τ (M.op (M.op X0 X0) (σ (τ (M.op X1 X1))))) ∨ (k X2 (τ (M.op X1 X1))) = (M.op (τ (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4331 (τ (M.op X1 X1)) X2
       have i₂ := eq1194 X0 (τ (M.op X1 X1)) X1
       grind)
    | exact superpose eq1194 eq4331
    | (have j0 := eq4331 (τ (M.op X1 X1)) X2
       grind)
    | exact resolve eq4331 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq4331
  have eq4363 : ∀ X0 X1 X2 : G, (τ (M.op X1 X1)) ≠ (k (τ (M.op X1 X1)) (τ (M.op X0 X0))) ∨ (k X2 (τ (M.op X1 X1))) = (M.op (τ (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4360 X0 X1 X2
       have i₂ := eq527 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq527 eq4360
    | (have j0 := eq4360 X0 X1 X2
       grind)
    | exact resolve eq4360 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4360
  have eq4368 : ∀ X0 X1 X2 : G, (τ (M.op X1 X1)) ≠ (τ (k (M.op X1 X1) (M.op X0 X0))) ∨ (k X2 (τ (M.op X1 X1))) = (M.op (τ (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4363 X0 X1 X2
       have i₂ := eq31 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact superpose eq31 eq4363
    | (have j0 := eq4363 X0 X1 X2
       grind)
    | exact resolve eq4363 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4363
  have eq4373 : ∀ X0 X1 X2 : G, (τ (M.op X1 X1)) ≠ (τ (M.op (M.op X0 X0) (M.op X1 X1))) ∨ (k X2 (τ (M.op X1 X1))) = (M.op (τ (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4368 X0 X1 X2
       have i₂ := eq258 X0 (M.op X1 X1)
       grind)
    | exact superpose eq258 eq4368
    | (have j0 := eq4368 X0 X1 X2
       grind)
    | exact resolve eq4368 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4368
  have eq4376 : ∀ X1 X2 : G, (k X2 (τ (M.op X1 X1))) = (M.op (τ (M.op X1 X1)) X2) := by
    intro X1 X2
    first
    | (have j0 := eq4373 x X1 X2
       grind)
    | (have r₁ := eq4373 X2 X1 X2
       have r₂ := eq2010 X1 X1 X2
       grind)
    | (have r₁ := eq4373 (M.op X1 X1) (M.op X1 X1) X2
       have r₂ := eq2010 (M.op (M.op X1 X1) (M.op X1 X1)) X1 X1
       grind)
    | exact resolve eq4373 eq2010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4373
  have eq4409 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 X1))) = (M.op (τ (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4376 X2 X0
       have i₂ := eq1268 X0 X2 X1
       grind)
    | (have i₁ := eq4376 X2 X0
       have i₂ := eq1268 X0 X1 X2
       grind)
    | exact superpose eq1268 eq4376
    | exact resolve eq4376 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq4442 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1844
       have i₂ := eq529 x y
       grind)
    | exact superpose eq529 eq1844
    | (have j1 := eq529 x (σ y)
       grind)
    | exact resolve eq1844 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529 eq1844
  have eq4443 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq4442
  have eq4445 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq4443
       have i₂ := eq82 X0 (σ y)
       grind)
    | (have i₁ := eq4443
       have i₂ := eq82 (σ y) X0
       grind)
    | exact superpose eq82 eq4443
    | exact resolve eq4443 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4443
  have eq5151 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq2010 X0 x x
       have i₂ := eq4445 (M.op x x)
       grind)
    | exact superpose eq4445 eq2010
    | exact resolve eq2010 eq4445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010 eq4445
  have eq5188 : ∀ X0 : G, y = (τ (M.op X0 X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq5151 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5151
    | exact resolve eq5151 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5151
  have eq6014 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (τ (M.op X0 X0)) (τ (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82 (τ (M.op X0 X0)) X2
       have i₂ := eq4409 (τ (M.op X0 X0)) X1 X0
       grind)
    | exact superpose eq4409 eq82
    | exact resolve eq82 eq4409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4409
  have eq6159 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (τ (k (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6014 X0 X1 X2
       have i₂ := eq31 (M.op X1 X1) (M.op X0 X0)
       grind)
    | exact superpose eq31 eq6014
    | exact resolve eq6014 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq6014
  have eq6275 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (τ (M.op (M.op X1 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6159 X0 X1 X2
       have i₂ := eq258 X1 (M.op X0 X0)
       grind)
    | exact superpose eq258 eq6159
    | exact resolve eq6159 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq6159
  have eq6589 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq5188 (M.op x x)
       have i₂ := eq6275 x x X0
       grind)
    | exact superpose eq6275 eq5188
    | exact resolve eq5188 eq6275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5188
  have eq6599 : y = (M.op y y) := by
    first
    | (have j0 := eq6589 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6589
  have eq6674 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq6599
       have i₂ := eq82 X0 y
       grind)
    | (have i₁ := eq6599
       have i₂ := eq82 y X0
       grind)
    | exact superpose eq82 eq6599
    | exact resolve eq6599 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq6599
  have eq6855 : ∀ X0 X1 : G, (M.op y (M.op (M.op X1 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X1 X0
       have i₂ := eq6674 X0
       grind)
    | exact superpose eq6674 eq307
    | exact resolve eq307 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq6884 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq6275 x x X0
       have i₂ := eq6674 (M.op x x)
       grind)
    | exact superpose eq6674 eq6275
    | exact resolve eq6275 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6275
  have eq6907 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X1)) X0 X1
       have i₂ := eq6674 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq6674 eq9
    | exact resolve eq9 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6923 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq6907 X0 x
       have i₂ := eq6674 x
       grind)
    | exact superpose eq6674 eq6907
    | exact resolve eq6907 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6907
  have eq6940 : y = (τ y) := by
    first
    | (have i₁ := eq6884 x
       have i₂ := eq6674 x
       grind)
    | exact superpose eq6674 eq6884
    | exact resolve eq6884 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6884
  have eq6963 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq6855 X0 x
       have i₂ := eq6674 x
       grind)
    | exact superpose eq6674 eq6855
    | exact resolve eq6855 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6855
  have eq7110 : y = (σ y) := by
    first
    | (have i₁ := eq11 y
       have i₂ := eq6940
       grind)
    | exact superpose eq6940 eq11
    | exact resolve eq11 eq6940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7129 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7110
       grind)
    | exact superpose eq7110 eq16
    | exact resolve eq16 eq7110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7110
  have eq7384 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1) = (M.op X0 (M.op (M.op (M.op X4 X4) y) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1000 X0 X1 X2 X3 X4 x
       have i₂ := eq6674 x
       grind)
    | exact superpose eq6674 eq1000
    | exact resolve eq1000 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq7385 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1) = (M.op X0 (M.op (M.op y (M.op X4 X4)) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7384 X0 X1 X2 X3 X4
       have i₂ := eq6923 (M.op X4 X4)
       grind)
    | exact superpose eq6923 eq7384
    | exact resolve eq7384 eq6923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7384
  have eq7386 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1) = (M.op X0 (M.op (M.op y y) (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7385 X0 X1 X2 X3 x
       have i₂ := eq6674 x
       grind)
    | exact superpose eq6674 eq7385
    | exact resolve eq7385 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7385
  have eq7387 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1) = (M.op X0 (M.op y (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7386 X0 X1 X2 X3
       have i₂ := eq6674 y
       grind)
    | exact superpose eq6674 eq7386
    | exact resolve eq7386 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7386
  have eq7388 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y (M.op X1 X0))) = (M.op (M.op (M.op X2 X2) y) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7387 X0 X1 X2 x
       have i₂ := eq6674 x
       grind)
    | exact superpose eq6674 eq7387
    | exact resolve eq7387 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7387
  have eq7389 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y (M.op X1 X0))) = (M.op (M.op y (M.op X2 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7388 X0 X1 X2
       have i₂ := eq6923 (M.op X2 X2)
       grind)
    | exact superpose eq6923 eq7388
    | exact resolve eq7388 eq6923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7388
  have eq7390 : ∀ X0 X1 : G, (M.op (M.op y y) X1) = (M.op X0 (M.op y (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7389 X0 X1 x
       have i₂ := eq6674 x
       grind)
    | exact superpose eq6674 eq7389
    | exact resolve eq7389 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7389
  have eq7391 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 (M.op y (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7390 X0 X1
       have i₂ := eq6674 y
       grind)
    | exact superpose eq6674 eq7390
    | exact resolve eq7390 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7390
  have eq7553 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq7391 (M.op X0 y) y
       have i₂ := eq7391 y X0
       grind)
    | exact superpose eq7391 eq7391
    | exact resolve eq7391 eq7391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7638 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq7553 X0
       have i₂ := eq6674 y
       grind)
    | exact superpose eq6674 eq7553
    | exact resolve eq7553 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7553
  have eq9708 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1113 y y X0 X1
       have i₂ := eq7638 y
       grind)
    | exact superpose eq7638 eq1113
    | exact resolve eq1113 eq7638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113 eq7638
  have eq10700 : ∀ X0 : G, (τ (M.op (σ X0) y)) = (k X0 (τ (M.op (M.op (σ X0) y) (M.op (σ X0) y)))) := by
    intro X0
    first
    | (have i₁ := eq527 (M.op (σ X0) y) X0
       have i₂ := eq9708 (σ X0) (M.op (σ X0) y)
       grind)
    | exact superpose eq9708 eq527
    | exact resolve eq527 eq9708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq9708
  have eq10753 : ∀ X0 : G, (τ (M.op (σ X0) y)) = (M.op (τ (M.op (M.op (σ X0) y) (M.op (σ X0) y))) X0) := by
    intro X0
    first
    | (have i₁ := eq10700 X0
       have i₂ := eq4376 (M.op (σ X0) y) X0
       grind)
    | exact superpose eq4376 eq10700
    | exact resolve eq10700 eq4376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4376 eq10700
  have eq10857 : ∀ X0 : G, (M.op (τ y) X0) = (τ (M.op (σ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq10753 X0
       have i₂ := eq6674 (M.op (σ X0) y)
       grind)
    | exact superpose eq6674 eq10753
    | exact resolve eq10753 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6674 eq10753
  have eq10916 : ∀ X0 : G, (τ (M.op y (σ X0))) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq10857 X0
       have i₂ := eq6923 (σ X0)
       grind)
    | exact superpose eq6923 eq10857
    | exact resolve eq10857 eq6923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10857
  have eq10941 : ∀ X0 : G, (M.op y X0) = (τ (M.op y (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10916 X0
       have i₂ := eq6940
       grind)
    | exact superpose eq6940 eq10916
    | exact resolve eq10916 eq6940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6940 eq10916
  have eq12093 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op y (σ X0))
       have i₂ := eq10941 X0
       grind)
    | exact superpose eq10941 eq11
    | exact resolve eq11 eq10941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10941
  have eq14772 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (σ (M.op y (M.op X0 y)))) := by
    intro X0
    first
    | (have i₁ := eq12093 (M.op y (M.op X0 y))
       have i₂ := eq7391 y X0
       grind)
    | exact superpose eq7391 eq12093
    | exact resolve eq12093 eq7391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7391
  have eq14812 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (M.op y (σ (M.op X0 y)))) := by
    intro X0
    first
    | (have i₁ := eq14772 X0
       have i₂ := eq12093 (M.op X0 y)
       grind)
    | exact superpose eq12093 eq14772
    | exact resolve eq14772 eq12093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14772
  have eq14834 : ∀ X0 : G, (σ (M.op y X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq14812 X0
       have i₂ := eq6963 (σ (M.op X0 y))
       grind)
    | exact superpose eq6963 eq14812
    | exact resolve eq14812 eq6963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6963 eq14812
  have eq14850 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq14834 X0
       have i₂ := eq12093 X0
       grind)
    | exact superpose eq12093 eq14834
    | exact resolve eq14834 eq12093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12093 eq14834
  have eq16466 : (M.op (σ x) y) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq7129
       have i₂ := eq14850 x
       grind)
    | exact superpose eq14850 eq7129
    | exact resolve eq7129 eq14850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7129 eq14850
  have eq16495 : False := by grind
  exact eq16495
