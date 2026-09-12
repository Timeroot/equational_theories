import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq19 X2 X0 x
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op x x) (M.op X0 x)
       have i₂ := eq19 X0 x x
       grind)
    | exact superpose eq19 eq12
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq40
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
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
  have eq89 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 x) x) X0
       have i₂ := eq20 X0 x x
       grind)
    | exact superpose eq20 eq12
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op (M.op X0 X1) X2) X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 x) x) X0
       have i₂ := eq20 X0 x x
       grind)
    | exact superpose eq20 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq102 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X2 X0))
       have i₂ := eq25 X0 X1 X2
       grind)
    | exact superpose eq25 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 (τ X1)) (k X2 (τ X3)))) = (k (k (σ X0) X1) (k (σ X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38 X2 X3 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq38
    | exact resolve eq38 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq392 : ∀ X0 X1 X2 : G, (σ (M.op X0 (τ X1))) = (k X1 (σ (M.op X2 (M.op X0 (τ X1))))) ∨ (M.op X0 (τ X1)) = (M.op X2 (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 (M.op X1 (M.op X2 (τ X1))) X1
       have i₂ := eq25 (τ X1) X1 X2
       grind)
    | exact superpose eq25 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq79
  have eq3248 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq78
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3309 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3248 X0 X1
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq3248
    | (have j0 := eq3248 X0 X1
       grind)
    | exact resolve eq3248 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3248
  have eq3360 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3309 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3309
  have eq3390 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3360 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3360
  have eq3447 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3390 (M.op x x)
       have i₂ := eq19 x x x
       grind)
    | exact superpose eq19 eq3390
    | (have j0 := eq3390 X0
       grind)
    | exact resolve eq3390 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3451 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq3390 X0
       grind)
    | exact superpose eq3390 eq12
    | (have j1 := eq3390 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3390 X0
       grind)
    | exact resolve eq12 eq3390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3390
  have eq3481 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3451 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3451
  have eq3504 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3481 X0
       grind)
    | exact superpose eq3481 eq11
    | (have j1 := eq3481 X0
       grind)
    | exact resolve eq11 eq3481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3481
  have eq3599 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3504 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3504
    | (have j0 := eq3504 X0
       grind)
    | exact resolve eq3504 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3504
  have eq3754 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3599 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3599
  have eq3975 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq3447 X0
       grind)
    | exact superpose eq3447 eq12
    | (have j1 := eq3447 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3447 X0
       grind)
    | exact resolve eq12 eq3447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447
  have eq4006 : ∀ X0 : G, (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3975 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3975
  have eq4586 : ∀ X0 : G, (τ (σ X0)) = (τ (k (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4006 (σ x)
       have i₂ := eq77 x x
       grind)
    | exact superpose eq77 eq4006
    | (have j0 := eq4006 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | exact resolve eq4006 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq4006
  have eq4642 : ∀ X0 : G, (τ (σ X0)) = (τ (k (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4586 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4586
  have eq4691 : ∀ X0 : G, (τ (σ X0)) = (τ (k (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4642 X0
       have j1 := eq3754 (σ X0)
       grind)
    | (have r₁ := eq4642 X0
       have r₂ := eq3754 (σ X0)
       grind)
    | exact resolve eq4642 eq3754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3754 eq4642
  have eq4698 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (k X0 X0))) (k X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4691 X0
       have i₂ := eq32 (σ (k X0 X0)) (k X0 X0)
       grind)
    | exact superpose eq32 eq4691
    | (have j0 := eq4691 X0
       grind)
    | exact resolve eq4691 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4691
  have eq4704 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) (k X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4698 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq4698
    | (have j0 := eq4698 X0
       grind)
    | exact resolve eq4698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4698
  have eq4710 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4704 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4704
    | (have j0 := eq4704 X0
       grind)
    | exact resolve eq4704 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4704
  have eq4716 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4710 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4710
    | (have j0 := eq4710 X0
       grind)
    | exact resolve eq4710 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4710
  have eq4869 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq229 (τ X0) X0 (τ X0) X0
       have i₂ := eq4716 (τ X0)
       grind)
    | exact superpose eq4716 eq229
    | (have j1 := eq4716 (τ X0)
       grind)
    | exact resolve eq229 eq4716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq4716
  have eq4898 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4869 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4869
    | (have j0 := eq4869 X0
       grind)
    | exact resolve eq4869 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4869
  have eq4909 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4898 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq4898
    | (have j0 := eq4898 X0
       grind)
    | exact resolve eq4898 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4898
  have eq4918 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4909 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4909
    | (have j0 := eq4909 X0
       grind)
    | exact resolve eq4909 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4909
  have eq4927 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4918 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq4918
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq4918 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4918
  have eq4963 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4927 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4927
  have eq4976 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq4963 X0
       have j1 := eq34 X0 X0 X0
       grind)
    | (have r₁ := eq4963 x
       have r₂ := eq34 x x x
       grind)
    | exact resolve eq4963 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq4963
  have eq4997 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4976 (M.op x x)
       have i₂ := eq19 x x x
       grind)
    | exact superpose eq19 eq4976
    | exact resolve eq4976 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4976
  have eq5102 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq190 X0 X0
       have i₂ := eq4997 X0
       grind)
    | exact superpose eq4997 eq190
    | (have j0 := eq190 X0 X0
       grind)
    | exact resolve eq190 eq4997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq5137 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4997 (σ X0)
       grind)
    | exact superpose eq4997 eq15
    | exact resolve eq15 eq4997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5149 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq4997 (τ X0)
       grind)
    | exact superpose eq4997 eq43
    | exact resolve eq43 eq4997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq5184 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5102 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5102
  have eq5210 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5149 X0
       have i₂ := eq4997 X0
       grind)
    | exact superpose eq4997 eq5149
    | exact resolve eq5149 eq4997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5149
  have eq5218 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5137 X0
       have i₂ := eq4997 X0
       grind)
    | exact superpose eq4997 eq5137
    | exact resolve eq5137 eq4997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4997 eq5137
  have eq5620 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) (σ X0) X1
       have i₂ := eq5218 X0
       grind)
    | exact superpose eq5218 eq19
    | exact resolve eq19 eq5218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6377 : ∀ X0 X2 : G, (σ X0) ≠ (M.op (σ X0) X2) ∨ (σ X0) = (k (M.op (σ X0) X2) (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq89 (σ (M.op X0 X0)) (M.op (σ X0) x) X2
       have i₂ := eq5620 X0 x
       grind)
    | exact superpose eq5620 eq89
    | exact resolve eq89 eq5620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq6378 : ∀ X0 X2 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (M.op (σ X0) X2) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq90 (σ (M.op X0 X0)) (M.op (σ X0) x) X2
       have i₂ := eq5620 X0 x
       grind)
    | exact superpose eq5620 eq90
    | exact resolve eq90 eq5620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq5620
  have eq6393 : ∀ X0 X2 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (M.op (σ X0) X2) (σ (M.op X0 X0))) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq6378 X0 X2
       have i₂ := eq5218 (M.op X0 X0)
       grind)
    | exact superpose eq5218 eq6378
    | (have j0 := eq6378 X0 X2
       grind)
    | exact resolve eq6378 eq5218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6378
  have eq6433 : ∀ X0 X2 : G, (σ X0) = (k (M.op (σ X0) X2) (σ (M.op X0 X0))) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq6393 X0 X2
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq6393 X0 X2
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq6393
    | (have j0 := eq6393 X0 X2
       grind)
    | exact resolve eq6393 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6393
  have eq6447 : ∀ X0 X2 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (M.op (σ X0) X2) (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have j0 := eq6433 X0 X2
       have j1 := eq6377 X0 X2
       grind)
    | (have r₁ := eq6433 X0 X2
       have r₂ := eq6377 X0 X2
       grind)
    | exact resolve eq6433 eq6377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6377 eq6433
  have eq24288 : ∀ X0 X1 X2 : G, (k X1 (τ (σ (M.op X2 (M.op X0 (τ (σ X1))))))) = (τ (σ (M.op X0 (τ (σ X1))))) ∨ (M.op X0 (τ (σ X1))) = (M.op X2 (M.op X0 (τ (σ X1)))) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 X1 (σ (M.op X2 (M.op X0 (τ (σ X1)))))
       have i₂ := eq392 X0 (σ X1) X2
       grind)
    | exact superpose eq392 eq40
    | (have j1 := eq392 X0 (σ X1) X2
       grind)
    | exact resolve eq40 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq392
  have eq24339 : ∀ X0 X1 X2 : G, (M.op X0 (τ (σ X1))) = (k X1 (τ (σ (M.op X2 (M.op X0 (τ (σ X1))))))) ∨ (M.op X0 (τ (σ X1))) = (M.op X2 (M.op X0 (τ (σ X1)))) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24288 X0 X1 X2
       have i₂ := eq10 (M.op X0 (τ (σ X1)))
       grind)
    | exact superpose eq10 eq24288
    | (have j0 := eq24288 X0 X1 X2
       grind)
    | exact resolve eq24288 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24288
  have eq24405 : ∀ X0 X1 X2 : G, (M.op X0 (τ (σ X1))) = (k X1 (M.op X2 (M.op X0 (τ (σ X1))))) ∨ (M.op X0 (τ (σ X1))) = (M.op X2 (M.op X0 (τ (σ X1)))) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24339 X0 X1 X2
       have i₂ := eq10 (M.op X2 (M.op X0 (τ (σ X1))))
       grind)
    | exact superpose eq10 eq24339
    | (have j0 := eq24339 X0 X1 X2
       grind)
    | exact resolve eq24339 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24339
  have eq24444 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 (M.op X2 (M.op X0 X1))) ∨ (M.op X0 (τ (σ X1))) = (M.op X2 (M.op X0 (τ (σ X1)))) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24405 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24405
    | (have j0 := eq24405 X0 X1 X2
       grind)
    | exact resolve eq24405 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24405
  have eq24475 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 (M.op X2 (M.op X0 X1))) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24444 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24444
    | (have j0 := eq24444 X0 X1 X2
       grind)
    | exact resolve eq24444 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24444
  have eq24497 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24475 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24475
    | (have j0 := eq24475 X0 X1 X2
       grind)
    | exact resolve eq24475 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24475
  have eq24509 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 (M.op X2 (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq24497 X0 X1 X2
       have j1 := eq102 X0 X1 X2
       grind)
    | (have r₁ := eq24497 X0 X1 X2
       have r₂ := eq102 X0 X1 X2
       grind)
    | (have r₁ := eq24497 X0 X1 X0
       have r₂ := eq102 X0 (M.op X0 X1) X2
       grind)
    | exact resolve eq24497 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq24497
  have eq27710 : ∀ X0 X2 X3 : G, (k (M.op X0 X2) (M.op X3 X0)) = X0 ∨ (M.op X3 X0) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq24509 (M.op X0 x) (M.op x x) X2
       have i₂ := eq19 X0 x x
       grind)
    | exact superpose eq19 eq24509
    | exact resolve eq24509 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27777 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24509 x x (M.op X0 x)
       have i₂ := eq19 X0 x x
       grind)
    | exact superpose eq19 eq24509
    | exact resolve eq24509 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24509
  have eq28025 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq27777 (σ X0) (σ X1)
       grind)
    | exact superpose eq27777 eq15
    | (have j1 := eq27777 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq27777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28029 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq27777 X0 (τ X1)
       grind)
    | exact superpose eq27777 eq17
    | (have j1 := eq27777 X0 (τ X1)
       grind)
    | exact resolve eq17 eq27777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq27777
  have eq28533 : ∀ X0 X1 : G, (σ X0) = (k (M.op (σ X0) X1) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27710 (σ X0) x (σ X0)
       have i₂ := eq5218 X0
       grind)
    | exact superpose eq5218 eq27710
    | exact resolve eq27710 eq5218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27710
  have eq28628 : ∀ X0 X1 : G, (σ X0) = (k (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq28533 X0 X1
       have j1 := eq6447 X0 X1
       grind)
    | (have r₁ := eq28533 X0 X1
       have r₂ := eq6447 X0 x
       grind)
    | exact resolve eq28533 eq6447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6447 eq28533
  have eq28743 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op (σ (τ X0)) X1) (σ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28628 (τ X0) X1
       have i₂ := eq5210 X0
       grind)
    | exact superpose eq5210 eq28628
    | exact resolve eq28628 eq5210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5210 eq28628
  have eq28815 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op (σ (τ X0)) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28743 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq28743
    | exact resolve eq28743 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28743
  have eq28877 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28815 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28815
    | exact resolve eq28815 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28815
  have eq29216 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28877 (M.op X1 X0) (M.op X0 x)
       have i₂ := eq19 X1 X0 x
       grind)
    | exact superpose eq19 eq28877
    | exact resolve eq28877 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29289 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28877 (M.op X0 X0) X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | exact superpose eq19 eq28877
    | exact resolve eq28877 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28877
  have eq38372 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28029 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28029
    | exact resolve eq28029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28029
  have eq38639 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38372 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq38372
    | (have j0 := eq38372 X0 X1
       grind)
    | exact resolve eq38372 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38372
  have eq53020 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28025 x y
       grind)
    | exact superpose eq28025 eq16
    | (have j1 := eq28025 x y
       grind)
    | exact resolve eq16 eq28025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53208 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq28025 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28025
  have eq55542 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53020
       have i₂ := eq38639 y x
       grind)
    | exact superpose eq38639 eq53020
    | (have j1 := eq38639 (σ y) (σ x)
       grind)
    | (have r₁ := eq53020
       have r₂ := eq38639 y x
       grind)
    | exact resolve eq53020 eq38639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53020
  have eq55545 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq55542
  have eq55554 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 x y
       have i₂ := eq55545
       grind)
    | exact superpose eq55545 eq19
    | exact resolve eq19 eq55545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55555 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19 x y X0
       have i₂ := eq55545
       grind)
    | exact superpose eq55545 eq19
    | exact resolve eq19 eq55545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55545
  have eq55920 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55554 (M.op x x)
       have i₂ := eq55554 x
       grind)
    | exact superpose eq55554 eq55554
    | exact resolve eq55554 eq55554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55554
  have eq55996 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq55920
  have eq56035 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ x) (σ y)
       have i₂ := eq55996
       grind)
    | exact superpose eq55996 eq19
    | exact resolve eq19 eq55996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq55996
  have eq58597 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq56035 (M.op x (σ x))
       have i₂ := eq56035 x
       grind)
    | exact superpose eq56035 eq56035
    | exact resolve eq56035 eq56035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56035
  have eq58710 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq58597
  have eq58729 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq58710
       have i₂ := eq5218 x
       grind)
    | exact superpose eq5218 eq58710
    | exact resolve eq58710 eq5218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58710
  have eq58746 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5184 x
       have i₂ := eq58729
       grind)
    | exact superpose eq58729 eq5184
    | (have j0 := eq5184 x
       grind)
    | (have r₁ := eq5184 x
       have r₂ := eq58729
       grind)
    | exact resolve eq5184 eq58729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58729
  have eq58862 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq58746
  have eq58874 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq5184 x
       grind)
    | (have r₁ := eq58862
       have r₂ := eq5184 x
       grind)
    | exact resolve eq58862 eq5184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5184 eq58862
  have eq58882 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq58874
       have i₂ := eq5218 x
       grind)
    | exact superpose eq5218 eq58874
    | exact resolve eq58874 eq5218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58874
  have eq59370 : (τ (σ x)) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq58882
       grind)
    | exact superpose eq58882 eq10
    | exact resolve eq10 eq58882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59372 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (M.op x x)
       have i₂ := eq58882
       grind)
    | exact superpose eq58882 eq15
    | exact resolve eq15 eq58882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58882
  have eq59581 : ∀ X0 : G, (σ (k X0 x)) = (σ (k X0 (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq59372 X0
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq59372
    | exact resolve eq59372 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59372
  have eq59583 : x = (M.op x x) := by
    first
    | (have i₁ := eq59370
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq59370
    | exact resolve eq59370 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59370
  have eq59651 : ∀ X0 : G, x = (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq29289 x x
       have i₂ := eq59583
       grind)
    | exact superpose eq59583 eq29289
    | exact resolve eq29289 eq59583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29289 eq59583
  have eq60605 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq53208 x (M.op x X0)
       have i₂ := eq59651 X0
       grind)
    | exact superpose eq59651 eq53208
    | (have j0 := eq53208 x (M.op x X0)
       grind)
    | exact resolve eq53208 eq59651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53208 eq59651
  have eq60610 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op x X0))) := by
    intro X0
    first
    | (have j0 := eq60605 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60605
  have eq66168 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq60610 (M.op y x)
       have i₂ := eq55555 x
       grind)
    | exact superpose eq55555 eq60610
    | exact resolve eq60610 eq55555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55555 eq60610
  have eq66278 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq66168
  have eq66368 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66278
       grind)
    | exact superpose eq66278 eq16
    | exact resolve eq16 eq66278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66436 : (σ x) = (k (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq29216 (σ y) (σ x)
       have i₂ := eq66278
       grind)
    | exact superpose eq66278 eq29216
    | exact resolve eq29216 eq66278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29216 eq66278
  have eq66446 : (σ x) = (k (σ y) (σ (M.op x x))) := by
    first
    | (have i₁ := eq66436
       have i₂ := eq5218 x
       grind)
    | exact superpose eq5218 eq66436
    | exact resolve eq66436 eq5218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5218 eq66436
  have eq66477 : (σ x) = (σ (k y (M.op x x))) := by
    first
    | (have i₁ := eq66446
       have i₂ := eq15 y (M.op x x)
       grind)
    | exact superpose eq15 eq66446
    | exact resolve eq66446 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66446
  have eq66495 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq66477
       have i₂ := eq59581 y
       grind)
    | exact superpose eq59581 eq66477
    | exact resolve eq66477 eq59581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59581 eq66477
  have eq66855 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38639 y x
       have i₂ := eq66495
       grind)
    | exact superpose eq66495 eq38639
    | (have j0 := eq38639 y x
       grind)
    | exact resolve eq38639 eq66495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38639 eq66495
  have eq67063 : x = (M.op x y) := by
    first
    | (have r₁ := eq66855
       have r₂ := eq66368
       grind)
    | exact resolve eq66855 eq66368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66855
  have eq67381 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq66368
       have i₂ := eq67063
       grind)
    | exact superpose eq67063 eq66368
    | exact resolve eq66368 eq67063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66368 eq67063
  have eq67432 : False := by grind
  exact eq67432

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq98 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq136 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq137 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq98 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq98
    | exact resolve eq98 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq445 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq426 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq426
    | (have j0 := eq426 X0
       grind)
    | exact resolve eq426 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq448 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq445 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq445
    | (have j0 := eq445 X0
       grind)
    | exact resolve eq445 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq449 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq448 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq448 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq448 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq460 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq449 (σ X0)
       grind)
    | exact superpose eq449 eq15
    | exact resolve eq15 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq460 X0
       have i₂ := eq449 X0
       grind)
    | exact superpose eq449 eq460
    | exact resolve eq460 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449 eq460
  have eq658 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq7524 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) X0
       have i₂ := eq137 X0 X1
       grind)
    | exact superpose eq137 eq12
    | (have j1 := eq137 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) X0
       have r₂ := eq137 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) X1
       have r₂ := eq137 (M.op X1 (σ X1)) X1
       grind)
    | exact resolve eq12 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq7571 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq7524 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7524
  have eq8441 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7571 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7571
    | exact resolve eq7571 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8472 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq7571 X0 X1
       grind)
    | exact superpose eq7571 eq29
    | (have j1 := eq7571 X0 X1
       grind)
    | exact resolve eq29 eq7571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq7571
  have eq8555 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8472 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8472
    | (have j0 := eq8472 X0 X1
       grind)
    | exact resolve eq8472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8472
  have eq8563 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8441 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq8441
    | (have j0 := eq8441 X0 X1
       grind)
    | exact resolve eq8441 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8441
  have eq8615 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq8563 X1 X0
       grind)
    | exact superpose eq8563 eq11
    | (have j1 := eq8563 X1 X0
       grind)
    | exact resolve eq11 eq8563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8563
  have eq8748 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8615 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq8615
    | (have j0 := eq8615 X0 X1
       grind)
    | exact resolve eq8615 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8615
  have eq8787 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq8748 (τ X0) X1
       grind)
    | exact superpose eq8748 eq19
    | (have j1 := eq8748 (τ X0) X1
       grind)
    | exact resolve eq19 eq8748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8748
  have eq8956 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8555 (τ X1) X0
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq8555
    | (have j0 := eq8555 (τ X0) X1
       grind)
    | exact resolve eq8555 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq8555
  have eq9093 : ∀ X0 X1 : G, X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8956 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8956
    | (have j0 := eq8956 X0 X1
       grind)
    | exact resolve eq8956 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8956
  have eq9133 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9093 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9093
    | (have j0 := eq9093 X0 X1
       grind)
    | exact resolve eq9093 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9093
  have eq9268 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq9133 X1 X0
       grind)
    | exact superpose eq9133 eq11
    | (have j1 := eq9133 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq9133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9133
  have eq9403 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9268 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq9268
    | (have j0 := eq9268 X0 X1
       grind)
    | exact resolve eq9268 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9268
  have eq9536 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9403 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9403
    | (have j0 := eq9403 (τ (σ X0)) (τ (σ (k X0 X1)))
       grind)
    | exact resolve eq9403 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9403
  have eq9722 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9536 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq9536
    | (have j0 := eq9536 X0 X1
       grind)
    | exact resolve eq9536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9536
  have eq9729 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9722 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9722
    | (have j0 := eq9722 X0 X1
       grind)
    | exact resolve eq9722 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9722
  have eq10166 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8787 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8787
    | exact resolve eq8787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8787
  have eq10268 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10166 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq10166
    | (have j0 := eq10166 X0 X1
       grind)
    | exact resolve eq10166 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10166
  have eq10579 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9729 y x
       grind)
    | exact superpose eq9729 eq16
    | (have j1 := eq9729 x y
       grind)
    | exact resolve eq16 eq9729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9729
  have eq10644 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10579
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq10579
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq10579
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq10579
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq10579 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10645 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq10579
       have i₂ := eq10268 x y
       grind)
    | exact superpose eq10268 eq10579
    | (have j1 := eq10268 x y
       grind)
    | (have r₁ := eq10579
       have r₂ := eq10268 x y
       grind)
    | (have r₁ := eq10579
       have r₂ := eq10268 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq10579
       have r₂ := eq10268 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq10579 eq10268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10268 eq10579
  have eq10648 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by grind
  clear eq10645
  have eq10649 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq10648
  have eq10650 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq10644
  have eq10651 : x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq10650
  have eq10654 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10649
       grind)
    | exact superpose eq10649 eq16
    | exact resolve eq16 eq10649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10649
  have eq10655 : y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10654
       have r₂ := eq479 x
       grind)
    | exact resolve eq10654 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10654
  have eq10659 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq658 x y
       have i₂ := eq10655
       grind)
    | exact superpose eq10655 eq658
    | (have j0 := eq658 x y
       grind)
    | exact resolve eq658 eq10655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq10655
  have eq10672 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10659
  have eq10673 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq10672
  have eq10677 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10651
       grind)
    | exact superpose eq10651 eq16
    | exact resolve eq16 eq10651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10651
  have eq10678 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10677
       have r₂ := eq479 x
       grind)
    | exact resolve eq10677 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10677
  have eq11136 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10673
       grind)
    | exact superpose eq10673 eq16
    | exact resolve eq16 eq10673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10673
  have eq11178 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11136
       have i₂ := eq10678
       grind)
    | exact superpose eq10678 eq11136
    | exact resolve eq11136 eq10678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10678 eq11136
  have eq11179 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq11178
  have eq11180 : (σ x) = (σ y) := by grind
  clear eq11179
  have eq11181 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11180
       grind)
    | exact superpose eq11180 eq16
    | exact resolve eq16 eq11180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11182 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11180
       grind)
    | exact superpose eq11180 eq10
    | exact resolve eq10 eq11180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11180
  have eq11261 : x = y := by
    first
    | (have i₁ := eq11182
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11182
    | exact resolve eq11182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11182
  have eq11262 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11181
       have i₂ := eq479 x
       grind)
    | exact superpose eq479 eq11181
    | exact resolve eq11181 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq11181
  have eq11265 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11262
       have i₂ := eq11261
       grind)
    | exact superpose eq11261 eq11262
    | exact resolve eq11262 eq11261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11261 eq11262
  have eq11266 : False := by grind
  exact eq11266

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq14 X0 x x X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq70
    | (have j0 := eq70 (σ X0) (σ X1)
       grind)
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq76
    | (have j1 := eq70 y x
       grind)
    | exact resolve eq76 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq130 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq255 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq266 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq52 X2 X0 x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq70 (τ X1) X0
       grind)
    | exact superpose eq70 eq34
    | (have j1 := eq70 (τ X1) X0
       grind)
    | exact resolve eq34 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq377 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq652 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ X1)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X2 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq52
    | (have j1 := eq84 X0 X1
       grind)
    | exact resolve eq52 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq701 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq352
    | (have j0 := eq352 X0 (M.op x y)
       grind)
    | exact resolve eq352 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq764 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq377 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq377
    | (have j0 := eq377 x X0
       grind)
    | exact resolve eq377 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq377 X1 X0
       have i₂ := eq70 (σ X1) X0
       grind)
    | exact superpose eq70 eq377
    | (have j1 := eq70 (σ X1) X0
       grind)
    | exact resolve eq377 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq890 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq100 eq70
    | (have j0 := eq70 (σ y) (σ x)
       grind)
    | exact resolve eq70 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq891 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq890
    | exact resolve eq890 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq894 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq891
       have r₂ := eq27
       grind)
    | exact resolve eq891 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq897 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq894 eq266
    | exact resolve eq266 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq898 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq894 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq894
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq894
       grind)
    | exact resolve eq12 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq894 eq52
    | exact resolve eq52 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq911 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq898
  have eq912 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq911
    | exact resolve eq911 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq1073 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq897 eq905
    | exact resolve eq905 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897 eq905
  have eq1090 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1073
  have eq1094 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1090 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1090
       grind)
    | exact resolve eq13 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1107 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1094
  have eq1135 : (τ (σ x)) = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1107 eq49
    | exact resolve eq49 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1139 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq1135
    | exact resolve eq1135 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1142 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq70 x x
       have i₂ := eq1139
       grind)
    | exact superpose eq1139 eq70
    | (have j0 := eq70 x x
       grind)
    | exact resolve eq70 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq1143 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq1142
  have eq1147 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq265 y
       have i₂ := eq1143
       grind)
    | exact superpose eq1143 eq265
    | exact resolve eq265 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1155 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq52 y x X0
       have i₂ := eq1143
       grind)
    | exact superpose eq1143 eq52
    | exact resolve eq52 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1482 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1147 eq1155
    | exact resolve eq1155 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147 eq1155
  have eq1500 : x = (M.op x x) := by grind
  clear eq1482
  have eq1502 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq265 x
       have i₂ := eq1500
       grind)
    | exact superpose eq1500 eq265
    | exact resolve eq265 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq1503 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq1500
       grind)
    | exact superpose eq1500 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq1500
       grind)
    | exact resolve eq13 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1517 : x = (k x x) := by grind
  clear eq1503
  have eq1521 : x ≠ x ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq1502 eq13
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq1502
       grind)
    | exact resolve eq13 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1535 : x = (k (M.op x y) x) := by grind
  clear eq1521
  have eq1539 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1517
       grind)
    | exact superpose eq1517 eq43
    | exact resolve eq43 eq1517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1543 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1539
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1539
    | exact resolve eq1539 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1539
  have eq1545 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1535 eq130
    | exact resolve eq130 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1547 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1545
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1545
    | exact resolve eq1545 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545
  have eq1550 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1543 eq70
    | (have j0 := eq70 (σ x) (σ x)
       grind)
    | exact resolve eq70 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1551 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1550
  have eq1554 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1547
       have i₂ := eq70 sF1 sF2
       grind)
    | exact superpose eq70 eq1547
    | (have j1 := eq70 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq1547 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1569 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1551 eq52
    | exact resolve eq52 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2537 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1554 eq52
    | exact resolve eq52 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3584 : ∀ X0 : G, (k (k (σ x) (σ x)) (σ X0)) = (σ (M.op X0 (k x x))) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq49 eq349
    | exact resolve eq349 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq349
  have eq3632 : ∀ X0 : G, (k (k (σ x) (σ x)) (σ X0)) = (σ (M.op X0 x)) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3584 X0
       have i₂ := eq1517
       grind)
    | exact superpose eq1517 eq3584
    | (have j0 := eq3584 X0
       grind)
    | exact resolve eq3584 eq1517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3584
  have eq3637 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (M.op X0 x)) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1543 eq3632
    | (have j0 := eq3632 X0
       grind)
    | exact resolve eq3632 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543 eq3632
  have eq3639 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op X0 x)) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq35 eq3637
    | (have j0 := eq3637 X0
       grind)
    | exact resolve eq3637 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3637
  have eq3641 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op X0 x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3639 X0
       have i₂ := eq1517
       grind)
    | exact superpose eq1517 eq3639
    | (have j0 := eq3639 X0
       grind)
    | exact resolve eq3639 eq1517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517 eq3639
  have eq3751 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq3641 sF0
       grind)
    | exact superpose eq3641 eq45
    | (have j1 := eq3641 (M.op x y)
       grind)
    | exact resolve eq45 eq3641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3641
  have eq3801 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1502 eq3751
    | exact resolve eq3751 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3751
  have eq4743 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (σ (k X2 (τ X0)))) = X0 ∨ (M.op (σ X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq652 X0 (τ X0) X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq652
    | exact resolve eq652 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4848 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq45 eq652
    | (have j0 := eq652 x (M.op x y) x
       grind)
    | exact resolve eq652 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq652
  have eq4888 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq4848
    | (have j0 := eq4848 X0
       grind)
    | exact resolve eq4848 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4848
  have eq4920 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (k (σ X2) X0)) = X0 ∨ (M.op (σ X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4743 X0 X1 X2
       have i₂ := eq38 X0 X2
       grind)
    | exact superpose eq38 eq4743
    | (have j0 := eq4743 X0 X1 X2
       grind)
    | exact resolve eq4743 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq4743
  have eq4931 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq4888
    | (have j0 := eq4888 X0
       grind)
    | exact resolve eq4888 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4888
  have eq4962 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq4931 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4931
    | (have j0 := eq4931 X0
       grind)
    | exact resolve eq4931 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4931
  have eq6026 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq912 eq100
    | exact resolve eq100 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq6043 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6026
  have eq6201 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ (M.op x y))) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6043 eq52
    | exact resolve eq52 eq6043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq6203 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) X0)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6043 eq53
    | exact resolve eq53 eq6043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6208 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6043 eq267
    | exact resolve eq267 eq6043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq10469 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6043 eq6201
    | exact resolve eq6201 eq6043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6043 eq6201
  have eq10498 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10469
  have eq10591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10498 eq2537
    | exact resolve eq2537 eq10498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2537 eq10498
  have eq10615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10591
    | exact resolve eq10591 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10591
  have eq10616 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10615
       have r₂ := eq27
       grind)
    | exact resolve eq10615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10615
  have eq10696 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10616 eq6203
    | exact resolve eq6203 eq10616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6203 eq10616
  have eq10726 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10696
  have eq10730 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10726 eq894
    | exact resolve eq894 eq10726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq10726
  have eq10766 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10730
  have eq10775 : y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq255 x
       have i₂ := eq10766
       grind)
    | exact superpose eq10766 eq255
    | exact resolve eq255 eq10766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10766
  have eq10902 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10775 eq3801
    | exact resolve eq3801 eq10775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10775
  have eq10949 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10902
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10902
    | exact resolve eq10902 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10902
  have eq42952 : (σ (M.op x y)) = (M.op (σ x) (k (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1554 eq4962
    | exact resolve eq4962 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554 eq4962
  have eq43298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10949 eq42952
    | exact resolve eq42952 eq10949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10949
  have eq43340 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43298
  have eq43344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq43340
    | exact resolve eq43340 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43340
  have eq43347 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq43344
       have r₂ := eq27
       grind)
    | exact resolve eq43344 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43344
  have eq49490 : ∀ X0 : G, (k (k (M.op x y) x) (τ X0)) = (τ (M.op X0 (k (σ (M.op x y)) (σ x)))) ∨ (M.op (k (σ (M.op x y)) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq130 eq767
    | exact resolve eq767 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq767
  have eq49618 : ∀ X0 : G, (k (k (M.op x y) x) (τ X0)) = (τ (M.op X0 (σ x))) ∨ (M.op (k (σ (M.op x y)) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1547 eq49490
    | (have j0 := eq49490 X0
       grind)
    | exact resolve eq49490 eq1547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49490
  have eq49629 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 (σ x))) ∨ (M.op (k (σ (M.op x y)) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1535 eq49618
    | (have j0 := eq49618 X0
       grind)
    | exact resolve eq49618 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535 eq49618
  have eq49631 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (M.op X0 (σ x))) ∨ (M.op (k (σ (M.op x y)) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49629 X0
       have i₂ := eq764 X0
       grind)
    | exact superpose eq764 eq49629
    | (have j0 := eq49629 X0
       grind)
    | exact resolve eq49629 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq49629
  have eq49633 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (M.op X0 (σ x))) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1547 eq49631
    | (have j0 := eq49631 X0
       grind)
    | exact resolve eq49631 eq1547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547 eq49631
  have eq55576 : ∀ X0 : G, (M.op x y) = (M.op x (k (σ X0) (M.op x y))) ∨ (M.op x y) = (M.op (σ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1502 eq4920
    | (have j0 := eq4920 (M.op x y) x X0
       grind)
    | exact resolve eq4920 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4920
  have eq55969 : ∀ X0 : G, (M.op x y) = (M.op x (k X0 (M.op x y))) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq55576 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq55576
    | exact resolve eq55576 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55576
  have eq56128 : ∀ X0 : G, (M.op x y) = (M.op x (τ (k X0 (σ (M.op x y))))) ∨ (M.op x y) = (M.op (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq701 eq55969
    | (have j0 := eq55969 (τ X0)
       grind)
    | exact resolve eq55969 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq55969
  have eq58135 : (M.op x y) = (M.op x (τ (M.op (σ (M.op x y)) (σ x)))) ∨ (M.op x y) = (M.op (τ (σ x)) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq49633 eq56128
    | (have j0 := eq56128 (σ x)
       have j1 := eq49633 (σ (M.op x y))
       grind)
    | exact resolve eq56128 eq49633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49633 eq56128
  have eq58183 : (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x (τ (M.op (σ (M.op x y)) (σ x)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq28 eq58135
    | exact resolve eq58135 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58135
  have eq58227 : (M.op x y) = (M.op x (τ (M.op (σ (M.op x y)) (σ x)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1502 eq58183
    | exact resolve eq58183 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502 eq58183
  have eq298611 : (M.op x y) = (M.op x (τ (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43347 eq58227
    | exact resolve eq58227 eq43347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43347
  have eq298677 : (M.op x y) = (M.op x (τ (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq298611
  have eq298693 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq298677
    | exact resolve eq298677 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298677
  have eq298704 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq298693
       have i₂ := eq1500
       grind)
    | exact superpose eq1500 eq298693
    | exact resolve eq298693 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298693
  have eq298705 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq298704
  have eq298763 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq298705 eq1569
    | exact resolve eq1569 eq298705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299352 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq298763 eq298705
    | exact resolve eq298705 eq298763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298705 eq298763
  have eq299424 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq299352
  have eq299433 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq299424 eq67
    | (have r₁ := eq67
       have r₂ := eq299424
       grind)
    | exact resolve eq67 eq299424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq299424
  have eq299565 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq299433
  have eq299603 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq299565 eq100
    | exact resolve eq100 eq299565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq299565
  have eq299702 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq299603
  have eq299871 : y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq255 x
       have i₂ := eq299702
       grind)
    | exact superpose eq299702 eq255
    | exact resolve eq255 eq299702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299702
  have eq300733 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq299871 eq3801
    | exact resolve eq3801 eq299871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3801 eq299871
  have eq300905 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq300733
  have eq300933 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq300905
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq300905
    | exact resolve eq300905 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300905
  have eq302688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq300933 eq42952
    | exact resolve eq42952 eq300933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42952 eq300933
  have eq302732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq302688
  have eq302752 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq302732
    | exact resolve eq302732 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302732
  have eq302771 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq302752
       have r₂ := eq27
       grind)
    | exact resolve eq302752 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302752
  have eq303329 : (M.op x y) = (M.op x (τ (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq302771 eq58227
    | exact resolve eq58227 eq302771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58227 eq302771
  have eq303376 : (M.op x y) = (M.op x (τ (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq303329
  have eq303379 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq303376
    | exact resolve eq303376 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303376
  have eq303381 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq303379
       have i₂ := eq1500
       grind)
    | exact superpose eq1500 eq303379
    | exact resolve eq303379 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303379
  have eq303382 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq303381
  have eq303441 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq303382 eq1569
    | exact resolve eq1569 eq303382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq303544 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq303441 eq303382
    | exact resolve eq303382 eq303441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303382 eq303441
  have eq303611 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq303544
  have eq303622 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq303611 eq28
    | exact resolve eq28 eq303611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq303611
  have eq304426 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq303622
    | exact resolve eq303622 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq303622
  have eq304427 : x = (M.op x y) := by grind
  clear eq304426
  have eq304430 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq304427 eq20
    | exact resolve eq20 eq304427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq305008 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq304430
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq304430
    | exact resolve eq304430 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304430
  have eq305120 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq305008 eq26
    | exact resolve eq26 eq305008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq305170 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq305008 eq1551
    | exact resolve eq1551 eq305008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq307430 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq305170 eq6208
    | exact resolve eq6208 eq305170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6208
  have eq307476 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq305120 eq307430
    | exact resolve eq307430 eq305120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307430
  have eq307491 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq307476
       have r₂ := eq27
       grind)
    | exact resolve eq307476 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307476
  have eq307497 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq305008 eq307491
    | exact resolve eq307491 eq305008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307491
  have eq307498 : x = (M.op y x) := by
    first
    | (have r₁ := eq307497
       have r₂ := eq27
       grind)
    | exact resolve eq307497 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307497
  have eq312485 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq255 x
       have i₂ := eq307498
       grind)
    | exact superpose eq307498 eq255
    | exact resolve eq255 eq307498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq307498
  have eq312532 : y = (M.op x x) := by
    first
    | exact superpose eq304427 eq312485
    | exact resolve eq312485 eq304427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304427 eq312485
  have eq312596 : x = y := by
    first
    | (have i₁ := eq312532
       have i₂ := eq1500
       grind)
    | exact superpose eq1500 eq312532
    | exact resolve eq312532 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500 eq312532
  have eq312671 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq312596
       grind)
    | exact superpose eq312596 eq24
    | exact resolve eq24 eq312596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq312596
  have eq313442 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq312671
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq312671
    | exact resolve eq312671 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq312671
  have eq313660 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq305008 eq313442
    | exact resolve eq313442 eq305008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305008 eq313442
  have eq316072 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq313660 eq305120
    | exact resolve eq305120 eq313660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305120 eq313660
  have eq316079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq305170 eq316072
    | exact resolve eq316072 eq305170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305170 eq316072
  have eq316420 : False := by grind
  exact eq316420

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq88
    | exact resolve eq88 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 X0 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq477 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq112 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq112
    | (have j0 := eq112 (σ X0)
       grind)
    | exact resolve eq112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq44
    | (have j1 := eq112 x
       grind)
    | exact resolve eq44 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq3402 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq477 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq17966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17967 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17966
    | exact resolve eq17966 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17966
  have eq17978 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17967
       have r₂ := eq28
       grind)
    | exact resolve eq17967 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17967
  have eq17980 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17978
    | exact resolve eq17978 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17978
  have eq17982 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17980 eq252
    | exact resolve eq252 eq17980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17983 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17980 eq262
    | exact resolve eq262 eq17980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17980
  have eq18131 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17983 eq17982
    | exact resolve eq17982 eq17983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17982 eq17983
  have eq18182 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq18131
  have eq18189 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq18182
  have eq18234 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18189
    | exact resolve eq18189 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18189
  have eq18311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18234 eq91
    | exact resolve eq91 eq18234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq18234
  have eq18319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq18311
  have eq18321 : (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18319
       have r₂ := eq28
       grind)
    | exact resolve eq18319 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18319
  have eq18323 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq251 x
       have i₂ := eq18321
       grind)
    | exact superpose eq18321 eq251
    | exact resolve eq251 eq18321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq18324 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq261 y
       have i₂ := eq18321
       grind)
    | exact superpose eq18321 eq261
    | exact resolve eq261 eq18321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq18321
  have eq18519 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18324 eq18323
    | exact resolve eq18323 eq18324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18323 eq18324
  have eq18572 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18519
  have eq18580 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18572
  have eq18626 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18580
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18580
    | exact resolve eq18580 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18580
  have eq18855 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq18626
       grind)
    | exact superpose eq18626 eq45
    | exact resolve eq45 eq18626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq18626
  have eq18873 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq18855
    | exact resolve eq18855 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18855
  have eq18950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18873 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq18873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18950
    | exact resolve eq18950 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18950
  have eq18964 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18953
       have r₂ := eq28
       grind)
    | exact resolve eq18953 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18953
  have eq18966 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18964
    | exact resolve eq18964 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18964
  have eq32895 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18966 eq252
    | exact resolve eq252 eq18966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq32896 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18966 eq262
    | exact resolve eq262 eq18966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq18966
  have eq33700 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32896 eq32895
    | exact resolve eq32895 eq32896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32895 eq32896
  have eq33761 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq33700
  have eq33772 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq33761
  have eq33831 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq33772
    | exact resolve eq33772 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33772
  have eq34198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq33831 eq18873
    | exact resolve eq18873 eq33831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18873 eq33831
  have eq34216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq34198
  have eq34227 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq34216
       have r₂ := eq28
       grind)
    | exact resolve eq34216 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34216
  have eq34231 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq34227 eq30
    | exact resolve eq30 eq34227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq34227
  have eq34361 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq34231
    | exact resolve eq34231 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq34231
  have eq34362 : x = y := by grind
  clear eq34361
  have eq34645 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq34362
       grind)
    | exact superpose eq34362 eq19
    | exact resolve eq19 eq34362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq34646 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq34362
       grind)
    | exact superpose eq34362 eq25
    | exact resolve eq25 eq34362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq34362
  have eq34840 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq34646
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34646
    | exact resolve eq34646 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34646
  have eq34841 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq34840 eq27
    | exact resolve eq27 eq34840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq34840
  have eq34982 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq481
       have i₂ := eq34645
       grind)
    | exact superpose eq34645 eq481
    | exact resolve eq481 eq34645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq34994 : (M.op (M.op x y) x) = (k (M.op x y) x) := by grind
  have eq35048 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq34982
    | exact resolve eq34982 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34982
  have eq35473 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq39549 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35048 eq112
    | (have j0 := eq112 (σ x)
       grind)
    | exact resolve eq112 eq35048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq39550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34841 eq39549
    | exact resolve eq39549 eq34841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39549
  have eq39562 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq39550
       have r₂ := eq28
       grind)
    | exact resolve eq39550 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39550
  have eq39569 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34841 eq39562
    | exact resolve eq39562 eq34841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39562
  have eq39614 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39569 eq35473
    | exact resolve eq35473 eq39569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35473 eq39569
  have eq39615 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34841 eq39614
    | exact resolve eq39614 eq34841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39614
  have eq42891 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39615 eq35048
    | exact resolve eq35048 eq39615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35048 eq39615
  have eq42895 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq42891
  have eq42897 : x = (M.op x y) := by
    first
    | (have r₁ := eq42895
       have r₂ := eq28
       grind)
    | exact resolve eq42895 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42895
  have eq42909 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq42897 eq21
    | exact resolve eq21 eq42897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq43059 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq42897 eq34994
    | exact resolve eq34994 eq42897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34994
  have eq43065 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq43059
       have i₂ := eq34645
       grind)
    | exact superpose eq34645 eq43059
    | exact resolve eq43059 eq34645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34645 eq43059
  have eq43160 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq42909
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42909
    | exact resolve eq42909 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42909
  have eq43163 : x = (k x x) := by
    first
    | exact superpose eq42897 eq43065
    | exact resolve eq43065 eq42897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42897 eq43065
  have eq44213 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3402 x
       have i₂ := eq43163
       grind)
    | exact superpose eq43163 eq3402
    | (have j0 := eq3402 x
       grind)
    | exact resolve eq3402 eq43163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3402 eq43163
  have eq44217 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq44213
  have eq44225 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq44217
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44217
    | exact resolve eq44217 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq44217
  have eq44237 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34841 eq44225
    | exact resolve eq44225 eq34841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34841 eq44225
  have eq44248 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43160 eq44237
    | exact resolve eq44237 eq43160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43160 eq44237
  have eq44257 : False := by grind
  exact eq44257

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq32 : y = (τ (σ y)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq16 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X0 X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq178 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 x y X0
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X1 X0 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq178 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 X0 x y
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 (M.op X0 X0)
       have i₂ := eq178 X0 X0 X0
       grind)
    | exact superpose eq178 eq175
    | exact resolve eq175 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq204 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq204
    | exact resolve eq204 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq207 : y = (M.op (M.op x y) (k y y)) := by
    first
    | (have i₁ := eq193 y
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq193
    | exact resolve eq193 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq193 eq178
    | exact resolve eq178 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq220 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq198 eq178
    | exact resolve eq178 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (k X0 X1)) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X2 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq178
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq178
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : (M.op x y) = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq560
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq560
    | exact resolve eq560 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq582 : (M.op x y) = (k x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq553
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq553
    | exact resolve eq553 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq606 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (k X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq527 X0 X1 X2
       have i₂ := eq175 X1
       grind)
    | exact superpose eq175 eq527
    | (have j0 := eq527 X0 X1 X2
       grind)
    | exact resolve eq527 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq607 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (k X0 X1)) = X0 ∨ (k X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq526 X0 X1 X2
       have i₂ := eq175 X1
       grind)
    | exact superpose eq175 eq526
    | (have j0 := eq526 X0 X1 X2
       grind)
    | exact resolve eq526 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq894 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq582
       grind)
    | exact superpose eq582 eq41
    | exact resolve eq41 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq895 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq894
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq894
    | exact resolve eq894 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq897 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq20 eq895
    | exact resolve eq895 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq897 eq575
    | exact resolve eq575 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq897
  have eq987 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | (have r₁ := eq980
       have r₂ := eq27
       grind)
    | exact resolve eq980 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq992 : (τ (σ x)) = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq987 eq116
    | exact resolve eq116 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq987
  have eq1000 : x = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq992
    | exact resolve eq992 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1001 : x = (k y y) := by grind
  clear eq1000
  have eq1006 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq207
       have i₂ := eq1001
       grind)
    | exact superpose eq1001 eq207
    | exact resolve eq207 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq1008 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1001
       grind)
    | exact superpose eq1001 eq41
    | exact resolve eq41 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1009 : y = (k x x) := by
    first
    | (have i₁ := eq205 y
       have i₂ := eq1001
       grind)
    | exact superpose eq1001 eq205
    | exact resolve eq205 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1010 : ∀ X0 : G, y = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq195 y X0
       have i₂ := eq1001
       grind)
    | exact superpose eq1001 eq195
    | exact resolve eq195 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq1012 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1008
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1008
    | exact resolve eq1008 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1014 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1012
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1012
    | exact resolve eq1012 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1018 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq1006 eq198
    | exact resolve eq198 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq1021 : y = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1006 eq28
    | (have j0 := eq28 (M.op x y) x
       grind)
    | exact resolve eq28 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq1031 : (M.op x y) = (k x x) ∨ y = (k (M.op x y) x) := by
    first
    | (have i₁ := eq1021
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq1021
    | exact resolve eq1021 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1034 : y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1031
       have i₂ := eq1009
       grind)
    | exact superpose eq1009 eq1031
    | exact resolve eq1031 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1038 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1009
       grind)
    | exact superpose eq1009 eq40
    | exact resolve eq40 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1042 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1038
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1038
    | exact resolve eq1038 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1044 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1042
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1042
    | exact resolve eq1042 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1063 : x = (k y (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1018 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1073 : y = (k (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq1063
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq1063
    | exact resolve eq1063 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1082 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1044 eq190
    | exact resolve eq190 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq1127 : ∀ X0 : G, y = (M.op (k X0 y) x) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1010 X0
       have i₂ := eq28 X0 y
       grind)
    | exact superpose eq28 eq1010
    | (have j1 := eq28 X0 y
       grind)
    | exact resolve eq1010 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1010
  have eq1150 : ∀ X0 : G, (k y y) = X0 ∨ y = (M.op (k X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq1127 X0
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq1127
    | (have j0 := eq1127 X0
       grind)
    | exact resolve eq1127 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1155 : ∀ X0 : G, y = (M.op (k X0 y) x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq1150 X0
       have i₂ := eq1001
       grind)
    | exact superpose eq1001 eq1150
    | (have j0 := eq1150 X0
       grind)
    | exact resolve eq1150 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq1355 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1034 eq40
    | exact resolve eq40 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1034
  have eq1356 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1355
    | exact resolve eq1355 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq1358 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1356
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1356
    | exact resolve eq1356 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356
  have eq1579 : ∀ X0 X1 : G, (k X1 y) = (M.op (M.op X0 (k X1 y)) y) ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 (k X1 y) x
       have i₂ := eq1155 X1
       grind)
    | exact superpose eq1155 eq178
    | (have j1 := eq1155 X1
       grind)
    | exact resolve eq178 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq1155
  have eq1601 : (M.op x y) = (k y y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq1073 eq205
    | exact resolve eq205 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1604 : x = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1601
       have i₂ := eq1001
       grind)
    | exact superpose eq1001 eq1601
    | exact resolve eq1601 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1612 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1604 eq42
    | exact resolve eq42 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq1604
  have eq1613 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1612
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1612
    | exact resolve eq1612 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq1615 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1613
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1613
    | exact resolve eq1613 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613
  have eq11210 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1615 eq606
    | (have j0 := eq606 (σ y) (σ (M.op x y)) x
       grind)
    | exact resolve eq606 eq1615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq1615
  have eq11840 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1358 eq607
    | (have j0 := eq607 (σ (M.op x y)) (σ x) x
       grind)
    | exact resolve eq607 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq11894 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = X0 ∨ (k y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1579 (M.op x X0) X0
       have i₂ := eq607 X0 y x
       grind)
    | exact superpose eq607 eq1579
    | (have j0 := eq1579 X0 X0
       have j1 := eq607 X0 y x
       grind)
    | exact resolve eq1579 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607 eq1579
  have eq11929 : ∀ X0 : G, x = X0 ∨ (k X0 y) = (M.op X0 y) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq11894 X0
       have i₂ := eq1001
       grind)
    | exact superpose eq1001 eq11894
    | (have j0 := eq11894 X0
       grind)
    | exact resolve eq11894 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq11894
  have eq11930 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq11929 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11929
  have eq11935 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1044 eq11840
    | (have j0 := eq11840 X0
       grind)
    | exact resolve eq11840 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11840
  have eq12032 : ∀ X0 : G, (M.op x y) = (k (M.op X0 (M.op x y)) y) ∨ x = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq208 X0
       have i₂ := eq11930 (M.op X0 sF0)
       grind)
    | exact superpose eq11930 eq208
    | (have j1 := eq11930 (M.op X0 (M.op x y))
       grind)
    | exact resolve eq208 eq11930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq11930
  have eq13212 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op X0 (M.op x y))) (σ y)) ∨ x = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq12032 eq41
    | (have j1 := eq12032 X0
       grind)
    | exact resolve eq41 eq12032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq12032
  have eq13238 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op X0 (M.op x y))) (σ y)) ∨ x = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq13212
    | (have j0 := eq13212 X0
       grind)
    | exact resolve eq13212 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13212
  have eq15746 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11210 eq1082
    | exact resolve eq1082 eq11210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082 eq11210
  have eq15803 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15746 eq205
    | exact resolve eq205 eq15746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq15746
  have eq15813 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1014 eq15803
    | exact resolve eq15803 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15803
  have eq15832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15813 eq11935
    | exact resolve eq11935 eq15813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11935 eq15813
  have eq15865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15832
    | exact resolve eq15832 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15832
  have eq15869 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15865
       have r₂ := eq27
       grind)
    | exact resolve eq15865 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15865
  have eq15870 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15869 eq29
    | exact resolve eq29 eq15869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15869
  have eq15926 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq15870
    | exact resolve eq15870 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15870
  have eq15927 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15926
  have eq15939 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15927 eq29
    | exact resolve eq29 eq15927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15927
  have eq16004 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq15939
    | exact resolve eq15939 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15939
  have eq16005 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq16004
  have eq16010 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq16005
       grind)
    | exact superpose eq16005 eq18
    | exact resolve eq18 eq16005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16011 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq16005
       grind)
    | exact superpose eq16005 eq24
    | exact resolve eq24 eq16005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16170 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq16011
    | exact resolve eq16011 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16011
  have eq16249 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16010 eq13238
    | exact resolve eq13238 eq16010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13238 eq16010
  have eq16278 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16249
  have eq16284 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq16278
    | exact resolve eq16278 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16278
  have eq16290 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16170 eq16284
    | exact resolve eq16284 eq16170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16170 eq16284
  have eq16293 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1014 eq16290
    | exact resolve eq16290 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq16290
  have eq16295 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16293 eq32
    | exact resolve eq32 eq16293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq16293
  have eq16506 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq16295
    | exact resolve eq16295 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16295
  have eq16552 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16005 eq16506
    | exact resolve eq16506 eq16005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16005 eq16506
  have eq16553 : x = (M.op x y) := by grind
  clear eq16552
  have eq16574 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq16553
       grind)
    | exact superpose eq16553 eq18
    | exact resolve eq18 eq16553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq16575 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq16553
       grind)
    | exact superpose eq16553 eq22
    | exact resolve eq22 eq16553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq16585 : y = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1009
       have i₂ := eq16553
       grind)
    | exact superpose eq16553 eq1009
    | exact resolve eq1009 eq16553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq16708 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16575 eq20
    | exact resolve eq20 eq16575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq16886 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq16574 eq220
    | exact resolve eq220 eq16574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq16574
  have eq16927 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq16886
       have i₂ := eq16553
       grind)
    | exact superpose eq16553 eq16886
    | exact resolve eq16886 eq16553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16553 eq16886
  have eq16931 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq16927
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq16927
    | exact resolve eq16927 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16927
  have eq17052 : y = (M.op x y) := by
    first
    | exact superpose eq16931 eq16585
    | exact resolve eq16585 eq16931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16585 eq16931
  have eq17073 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq17052
       grind)
    | exact superpose eq17052 eq24
    | exact resolve eq24 eq17052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq17052
  have eq17309 : (σ x) = (σ y) := by
    first
    | exact superpose eq16575 eq17073
    | exact resolve eq17073 eq16575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16575 eq17073
  have eq17377 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17309 eq26
    | exact resolve eq26 eq17309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq17585 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq17377
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq17377
    | exact resolve eq17377 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq17377
  have eq17641 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1044 eq17585
    | exact resolve eq17585 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq17585
  have eq17670 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17309 eq17641
    | exact resolve eq17641 eq17309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17309 eq17641
  have eq18168 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq17670 eq27
    | exact resolve eq27 eq17670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17670
  have eq18220 : False := by grind
  exact eq18220

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq41 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq47
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq43 X0 X1
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq43 X0 X1
       grind)
    | exact resolve eq51 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq51
  have eq184 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq189 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       have j1 := eq53 X1 X0
       grind)
    | (have r₁ := eq184 X1 X0
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq184 X1 X1
       have r₂ := eq53 X1 X1
       grind)
    | exact resolve eq184 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq184
  have eq233 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq189 (σ X1) (σ X0)
       grind)
    | exact superpose eq189 eq15
    | exact resolve eq15 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq233 X0 X1
       have i₂ := eq189 X1 X0
       grind)
    | exact superpose eq189 eq233
    | exact resolve eq233 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq233
  have eq240 : False := by grind
  exact eq240

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
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
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
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
  have eq76 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq417 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq53 X1 x x X0
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq465 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op (M.op X1 X2) X0) X3) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq658 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X3)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 X3 X1 X2 (M.op (M.op X0 x) (M.op X0 (M.op (M.op X1 X2) X3)))
       have i₂ := eq54 (M.op (M.op X1 X2) X3) X0 x
       grind)
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X4) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq57 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq745 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1843 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq417 X1 X0
       grind)
    | exact superpose eq417 eq14
    | exact resolve eq14 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq5922 : ∀ X0 X3 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op (M.op y X0) X3) X0)) = X0 := by
    intro X0 X3
    first
    | exact superpose eq470 eq465
    | exact resolve eq465 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq6533 : ∀ X2 : G, (M.op y X2) = (M.op (M.op (M.op x y) (M.op y X2)) X2) := by
    intro X2
    first
    | exact superpose eq470 eq683
    | exact resolve eq683 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq6623 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0 X0 X1
       grind)
    | exact superpose eq54 eq683
    | exact resolve eq683 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq683
  have eq6742 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6623 X0 X1
       have i₂ := eq1843 X0 X0
       grind)
    | exact superpose eq1843 eq6623
    | exact resolve eq6623 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843 eq6623
  have eq15789 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq662 X1 (M.op X0 X2) x x (M.op X0 X1)
       have i₂ := eq658 (M.op (M.op (M.op (M.op X0 X2) x) X1) x) X0 X2 X1
       grind)
    | exact superpose eq658 eq662
    | exact resolve eq662 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq662
  have eq16530 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq446 (M.op X1 X0) X1 X0
       have i₂ := eq15789 X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq15789 eq446
    | exact resolve eq446 eq15789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq15789
  have eq51452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq51452
    | exact resolve eq51452 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51452
  have eq51466 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq51461
       have r₂ := eq28
       grind)
    | exact resolve eq51461 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51461
  have eq51468 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq51466
    | exact resolve eq51466 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51466
  have eq51496 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq51468
  have eq51608 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq51496
    | exact resolve eq51496 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51496
  have eq52472 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq51608 eq114
    | exact resolve eq114 eq51608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51608
  have eq52485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq52472
  have eq52487 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq52485
       have r₂ := eq28
       grind)
    | exact resolve eq52485 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52485
  have eq52517 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq52487
  have eq52629 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52517
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52517
    | exact resolve eq52517 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52517
  have eq53501 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq52629
       grind)
    | exact superpose eq52629 eq73
    | exact resolve eq73 eq52629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52629
  have eq53531 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq53501
    | exact resolve eq53501 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53501
  have eq53674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53531 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq53531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53685 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq53674
    | exact resolve eq53674 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53674
  have eq53690 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq53685
       have r₂ := eq28
       grind)
    | exact resolve eq53685 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53685
  have eq53692 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq53690
    | exact resolve eq53690 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53690
  have eq53693 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq53692
  have eq53722 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq53693
  have eq53834 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq53722
    | exact resolve eq53722 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53722
  have eq54355 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53834 eq53531
    | exact resolve eq53531 eq53834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53531 eq53834
  have eq54365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq54355
  have eq54369 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq54365
       have r₂ := eq28
       grind)
    | exact resolve eq54365 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54365
  have eq54371 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54369 eq28
    | exact resolve eq28 eq54369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54374 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54369 eq77
    | (have r₁ := eq77
       have r₂ := eq54369
       grind)
    | exact resolve eq77 eq54369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq54369
  have eq54465 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq54374
  have eq74085 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54465 eq114
    | exact resolve eq114 eq54465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74103 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq74085
  have eq74111 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq74103
       have r₂ := eq54371
       grind)
    | exact resolve eq74103 eq54371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74103
  have eq74238 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq74111
  have eq74367 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq74238
    | exact resolve eq74238 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74238
  have eq75218 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq74367 eq114
    | exact resolve eq114 eq74367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq74367
  have eq75232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq75218
  have eq75236 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq75232
       have r₂ := eq28
       grind)
    | exact resolve eq75232 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75232
  have eq75279 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq75236
  have eq75399 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75279
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75279
    | exact resolve eq75279 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75279
  have eq76117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq75399
       grind)
    | exact superpose eq75399 eq73
    | exact resolve eq73 eq75399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75399
  have eq76151 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq76117
    | exact resolve eq76117 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76117
  have eq76350 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76151 eq54465
    | exact resolve eq54465 eq76151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54465
  have eq76362 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq76350
  have eq76370 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq76362
       have r₂ := eq54371
       grind)
    | exact resolve eq76362 eq54371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54371 eq76362
  have eq76428 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq76370
  have eq76557 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq76428
    | exact resolve eq76428 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76428
  have eq77228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76557 eq76151
    | exact resolve eq76151 eq76557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76151 eq76557
  have eq77238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq77228
  have eq77246 : y = (M.op x y) := by
    first
    | (have r₁ := eq77238
       have r₂ := eq28
       grind)
    | exact resolve eq77238 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77238
  have eq77248 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq77246 eq21
    | exact resolve eq21 eq77246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq77255 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq77246 eq76
    | (have r₁ := eq76
       have r₂ := eq77246
       grind)
    | exact resolve eq76 eq77246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq77388 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y (M.op y X0)) X0) := by
    intro X0
    first
    | exact superpose eq77246 eq6533
    | exact resolve eq6533 eq77246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6533
  have eq77421 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq77255
  have eq77436 : ∀ X0 : G, (M.op X0 X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq77388 X0
       have i₂ := eq16530 X0 y
       grind)
    | exact superpose eq16530 eq77388
    | exact resolve eq77388 eq16530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16530 eq77388
  have eq77514 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq77248
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq77248
    | exact resolve eq77248 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77248
  have eq77515 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq77514 eq27
    | exact resolve eq27 eq77514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq80024 : ∀ X0 X3 : G, (M.op (M.op y X0) (M.op (M.op (M.op y X0) X3) X0)) = X0 := by
    intro X0 X3
    first
    | exact superpose eq77246 eq5922
    | exact resolve eq5922 eq77246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5922
  have eq80568 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq80024 X0 (M.op y y)
       have i₂ := eq6742 y X0
       grind)
    | exact superpose eq6742 eq80024
    | exact resolve eq80024 eq6742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6742 eq80024
  have eq80819 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq80568 X0
       have i₂ := eq77436 (M.op y X0)
       grind)
    | exact superpose eq77436 eq80568
    | exact resolve eq80568 eq77436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80568
  have eq80923 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 y (M.op y X0)
       have i₂ := eq80819 X0
       grind)
    | exact superpose eq80819 eq14
    | exact resolve eq14 eq80819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86291 : ∀ X0 : G, (M.op (M.op y X0) X0) = (k X0 (M.op y X0)) := by
    intro X0
    grind
  clear eq80923
  have eq94061 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq77421
       grind)
    | exact superpose eq77421 eq73
    | exact resolve eq73 eq77421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94080 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq745 x y
       have i₂ := eq77421
       grind)
    | exact superpose eq77421 eq745
    | (have j0 := eq745 x y
       grind)
    | exact resolve eq745 eq77421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77421
  have eq94081 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq94080
  have eq94088 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94081
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq94081
    | exact resolve eq94081 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94081
  have eq94105 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77514 eq94061
    | exact resolve eq94061 eq77514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94061
  have eq94107 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77514 eq94088
    | exact resolve eq94088 eq77514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94088
  have eq94123 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94105
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq94105
    | exact resolve eq94105 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94105
  have eq94124 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94107
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq94107
    | exact resolve eq94107 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94107
  have eq94139 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77514 eq94123
    | exact resolve eq94123 eq77514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94123
  have eq94140 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77515 eq94124
    | exact resolve eq94124 eq77515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94124
  have eq94148 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq94140
       have r₂ := eq28
       grind)
    | exact resolve eq94140 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94140
  have eq94156 : (σ y) = (M.op y (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94148
       have i₂ := eq77436 (σ x)
       grind)
    | exact superpose eq77436 eq94148
    | exact resolve eq94148 eq77436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94148
  have eq94164 : (σ y) = (M.op y (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94156
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq94156
    | exact resolve eq94156 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94156
  have eq94172 : (σ y) = (M.op y (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94164
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq94164
    | exact resolve eq94164 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94164
  have eq94180 : (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77514 eq94172
    | exact resolve eq94172 eq77514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94172
  have eq94258 : (σ x) = (M.op y (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq94180 eq80819
    | exact resolve eq80819 eq94180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94180
  have eq114308 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq94258 eq86291
    | exact resolve eq86291 eq94258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94258
  have eq114392 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77515 eq114308
    | exact resolve eq114308 eq77515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114308
  have eq114439 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq114392 eq94139
    | exact resolve eq94139 eq114392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94139 eq114392
  have eq114452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq114439
  have eq114465 : y = (M.op x x) := by
    first
    | (have r₁ := eq114452
       have r₂ := eq28
       grind)
    | exact resolve eq114452 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114452
  have eq114512 : (M.op x y) = (k y x) := by grind
  clear eq114465
  have eq114670 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq114512
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq114512
    | exact resolve eq114512 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq114512
  have eq114702 : y = (k y x) := by
    first
    | exact superpose eq77246 eq114670
    | exact resolve eq114670 eq77246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77246 eq114670
  have eq115082 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq114702
       grind)
    | exact superpose eq114702 eq73
    | exact resolve eq73 eq114702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq115101 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq745 x y
       have i₂ := eq114702
       grind)
    | exact superpose eq114702 eq745
    | (have j0 := eq745 x y
       grind)
    | exact resolve eq745 eq114702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq114702
  have eq115102 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq115101
  have eq115109 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq115102
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq115102
    | exact resolve eq115102 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115102
  have eq115125 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq77514 eq115082
    | exact resolve eq115082 eq77514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115082
  have eq115126 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq77514 eq115109
    | exact resolve eq115109 eq77514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115109
  have eq115142 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq115125
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq115125
    | exact resolve eq115125 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115125
  have eq115143 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq115126
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq115126
    | exact resolve eq115126 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115126
  have eq115158 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq77514 eq115142
    | exact resolve eq115142 eq77514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115142
  have eq115159 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq77515 eq115143
    | exact resolve eq115143 eq77515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115143
  have eq115167 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq115159
       have r₂ := eq28
       grind)
    | exact resolve eq115159 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115159
  have eq115175 : (σ y) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq115167
       have i₂ := eq77436 (σ x)
       grind)
    | exact superpose eq77436 eq115167
    | exact resolve eq115167 eq77436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77436 eq115167
  have eq115183 : (σ y) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq115175
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq115175
    | exact resolve eq115175 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq115175
  have eq115191 : (σ y) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq115183
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq115183
    | exact resolve eq115183 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq115183
  have eq115199 : (σ (M.op x y)) = (M.op y (σ x)) := by
    first
    | exact superpose eq77514 eq115191
    | exact resolve eq115191 eq77514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77514 eq115191
  have eq117693 : (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | exact superpose eq115199 eq80819
    | exact resolve eq80819 eq115199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80819 eq115199
  have eq118162 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq117693 eq86291
    | exact resolve eq86291 eq117693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86291 eq117693
  have eq118311 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq77515 eq118162
    | exact resolve eq118162 eq77515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77515 eq118162
  have eq118335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq115158 eq118311
    | exact resolve eq118311 eq115158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115158 eq118311
  have eq118349 : False := by grind
  exact eq118349

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxx_pyy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 y x X0
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 (σ y) (σ x) X0
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq99 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq99 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq99 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq108 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq108
    | exact resolve eq108 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq108
  have eq189 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq10
    | exact resolve eq10 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq189 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq189
    | exact resolve eq189 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq320 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq378 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x (M.op X1 X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq55
  have eq385 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq380 eq9
    | exact resolve eq9 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq513 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 X1 (M.op (M.op X0 x) (M.op X0 X1))
       have i₂ := eq54 X1 X0 x
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op (M.op (M.op x y) X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq560 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x X0) (M.op x y)) (M.op (M.op y X1) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq89 eq54
    | exact resolve eq54 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq562 : ∀ X0 : G, y = (M.op (M.op y y) (M.op (M.op (M.op x y) X0) y)) := by
    intro X0
    first
    | exact superpose eq385 eq54
    | exact resolve eq54 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq566 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (M.op (σ y) X1) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq93 eq54
    | exact resolve eq54 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq669 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
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
  have eq939 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X0 X1)
       have i₂ := eq378 X1 X0
       grind)
    | exact superpose eq378 eq9
    | exact resolve eq9 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq993 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq939 X1 (M.op X0 X0)
       have i₂ := eq939 X0 X0
       grind)
    | exact superpose eq939 eq939
    | exact resolve eq939 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1130 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq320 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq320
    | (have j0 := eq320 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq320 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq2359 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq545 (M.op sF0 X0) X0
       have i₂ := eq9 X0 sF0 (M.op sF0 X0)
       grind)
    | exact superpose eq9 eq545
    | exact resolve eq545 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq2391 : (M.op (M.op x y) (M.op x x)) = (M.op (M.op x x) (M.op x x)) := by
    first
    | exact superpose eq80 eq2359
    | exact resolve eq2359 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq2359
  have eq2430 : x = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq2391
       have i₂ := eq939 x x
       grind)
    | exact superpose eq939 eq2391
    | exact resolve eq2391 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2391
  have eq2439 : y = (M.op (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq2430 eq562
    | exact resolve eq562 eq2430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq2430
  have eq2458 : y = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq2439
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2439
    | exact resolve eq2439 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2439
  have eq2556 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq993 X0 X1
       grind)
    | exact superpose eq993 eq9
    | exact resolve eq9 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2575 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq57 (M.op sF3 sF3)
       have i₂ := eq993 sF3 sF2
       grind)
    | exact superpose eq993 eq57
    | exact resolve eq57 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq993
  have eq2759 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op X0 X0) X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X1 X0) (M.op X0 X0) X2
       have i₂ := eq2556 X0 X1
       grind)
    | exact superpose eq2556 eq54
    | exact resolve eq54 eq2556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq5858 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x X0) (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq2458 eq560
    | exact resolve eq560 eq2458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq2458
  have eq5887 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq5858 (M.op (M.op x X0) (M.op X0 x))
       have i₂ := eq513 x X0 x
       grind)
    | exact superpose eq513 eq5858
    | exact resolve eq5858 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6030 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq2575 eq566
    | exact resolve eq566 eq2575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq2575
  have eq6059 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6030 (M.op (M.op X0 x) (M.op x sF2))
       have i₂ := eq513 X0 x sF2
       grind)
    | exact superpose eq513 eq6030
    | exact resolve eq6030 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12530 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 (M.op (M.op X0 X0) X1) x X0
       have i₂ := eq2759 X0 (M.op (M.op (M.op (M.op X0 X0) X1) x) X0) X1
       grind)
    | exact superpose eq2759 eq56
    | exact resolve eq56 eq2759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq2759
  have eq12841 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12530 (M.op X1 X1) X1
       have i₂ := eq2556 X1 X1
       grind)
    | exact superpose eq2556 eq12530
    | exact resolve eq12530 eq2556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2556 eq12530
  have eq13354 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) (M.op X0 X0)
       have i₂ := eq12841 X0 X1
       grind)
    | exact superpose eq12841 eq9
    | exact resolve eq9 eq12841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14162 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op X1 (M.op (M.op X0 X1) X3)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq669 x (M.op (M.op X0 X1) (M.op X1 x)) x
       have i₂ := eq513 X0 X1 x
       grind)
    | exact superpose eq513 eq669
    | exact resolve eq669 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq669
  have eq15567 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op X0 x) (M.op x y)) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq5887 eq13354
    | exact resolve eq13354 eq5887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5887
  have eq15595 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq6059 eq13354
    | exact resolve eq13354 eq6059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6059 eq13354
  have eq69180 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op (M.op X0 x) (M.op x y)) (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq15567 eq14162
    | exact resolve eq14162 eq15567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15567
  have eq69196 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq15595 eq14162
    | exact resolve eq14162 eq15595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14162 eq15595
  have eq113829 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1130 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1130
    | (have j0 := eq1130 x y
       grind)
    | exact resolve eq1130 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq113877 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq113829
    | exact resolve eq113829 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113829
  have eq113878 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq113877
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq113877
    | exact resolve eq113877 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113877
  have eq113879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq113878
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq113878
    | exact resolve eq113878 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113878
  have eq113880 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq113879
    | exact resolve eq113879 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113879
  have eq113881 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq113880
       have r₂ := eq27
       grind)
    | exact resolve eq113880 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113880
  have eq113882 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq113881
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq113881
    | exact resolve eq113881 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113881
  have eq113883 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq113882
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq113882
    | exact resolve eq113882 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113882
  have eq113884 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq113883
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq113883
    | exact resolve eq113883 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113883
  have eq113946 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq113884 eq232
    | exact resolve eq232 eq113884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113884
  have eq114044 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq39 eq113946
    | exact resolve eq113946 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq113946
  have eq114062 : (M.op y y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq114044
       have i₂ := eq232 sF2
       grind)
    | exact superpose eq232 eq114044
    | exact resolve eq114044 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114044
  have eq114063 : (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38 eq114062
    | exact resolve eq114062 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114062
  have eq114064 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq114063
  have eq114160 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq114064 eq232
    | exact resolve eq232 eq114064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq114064
  have eq114265 : x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38 eq114160
    | exact resolve eq114160 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq114160
  have eq114266 : (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq114265
  have eq114439 : y = (M.op (M.op x x) (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12841 y y
       have i₂ := eq114266
       grind)
    | exact superpose eq114266 eq12841
    | exact resolve eq12841 eq114266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12841 eq114266
  have eq114459 : x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq114439
       have i₂ := eq939 x x
       grind)
    | exact superpose eq939 eq114439
    | exact resolve eq114439 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939 eq114439
  have eq114560 : (M.op y y) = (M.op (M.op (M.op x (M.op x y)) (M.op x y)) y) ∨ x = y := by
    first
    | (have i₁ := eq69180 x
       have i₂ := eq114459
       grind)
    | exact superpose eq114459 eq69180
    | exact resolve eq69180 eq114459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69180
  have eq114563 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq109 x
       have i₂ := eq114459
       grind)
    | exact superpose eq114459 eq109
    | exact resolve eq109 eq114459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114459
  have eq114671 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq114563
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq114563
    | exact resolve eq114563 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114563
  have eq114672 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq5858 eq114560
    | exact resolve eq114560 eq5858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5858 eq114560
  have eq114990 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) ∨ x = y := by
    first
    | exact superpose eq114671 eq69196
    | exact resolve eq69196 eq114671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69196 eq114671
  have eq115102 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq6030 eq114990
    | exact resolve eq114990 eq6030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6030 eq114990
  have eq115384 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq109 y
       have i₂ := eq114672
       grind)
    | exact superpose eq114672 eq109
    | exact resolve eq109 eq114672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114672
  have eq115480 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq115384
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq115384
    | exact resolve eq115384 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115384
  have eq115484 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq115480
    | exact resolve eq115480 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115480
  have eq116007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq115484 eq115102
    | exact resolve eq115102 eq115484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115102 eq115484
  have eq116138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq116007
  have eq116142 : x = y := by
    first
    | (have r₁ := eq116138
       have r₂ := eq27
       grind)
    | exact resolve eq116138 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116138
  have eq116153 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq116142
       grind)
    | exact superpose eq116142 eq18
    | exact resolve eq18 eq116142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq116154 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq116142
       grind)
    | exact superpose eq116142 eq24
    | exact resolve eq24 eq116142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq116142
  have eq124887 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq116154
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq116154
    | exact resolve eq116154 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116154
  have eq128106 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq124887 eq26
    | exact resolve eq26 eq124887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq124887
  have eq143169 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq109 x
       have i₂ := eq116153
       grind)
    | exact superpose eq116153 eq109
    | exact resolve eq109 eq116153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq116153
  have eq143814 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq143169
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq143169
    | exact resolve eq143169 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq143169
  have eq144006 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq128106 eq143814
    | exact resolve eq143814 eq128106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128106 eq143814
  have eq144045 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq144006
    | exact resolve eq144006 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq144006
  have eq144065 : False := by grind
  exact eq144065
