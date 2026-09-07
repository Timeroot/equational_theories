import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation433`: `x = x ◇ (y ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_y_x_pyx_Equation433 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law433 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law433.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 (M.op X1 X0)
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X0) X0
       have i₂ := eq23 X2 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq47 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq49 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq75 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq78 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq69
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq79 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq67
    | exact resolve eq67 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq89 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq148 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq78 (τ X0)
       grind)
    | exact superpose eq78 eq20
    | exact resolve eq20 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq78
  have eq149 : ∀ X0 : G, (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq148 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq148
    | exact resolve eq148 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq169 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0
       have i₂ := eq47 X0 X1
       grind)
    | (have i₁ := eq29 X0
       have i₂ := eq47 X0 (M.op X0 X0)
       grind)
    | exact superpose eq47 eq29
    | (have j1 := eq47 X1 X0
       grind)
    | exact resolve eq29 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq183 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq184 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq169 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq3629 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = X0 ∨ (k (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq183 (M.op X1 X0) X0
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq183
    | (have j0 := eq183 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq183 (M.op X0 X1) X1
       have r₂ := eq23 X0 X1
       grind)
    | exact resolve eq183 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq3647 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = X0 ∨ (k (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3629 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3629
  have eq3971 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X0
       have i₂ := eq49 X0 X1
       grind)
    | (have i₁ := eq25 X0 X1
       have i₂ := eq49 X0 (M.op X1 X0)
       grind)
    | exact superpose eq49 eq25
    | (have j1 := eq49 X1 X0
       grind)
    | exact resolve eq25 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq4012 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3971 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3971
  have eq4060 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4012 (σ X0) (σ X1)
       grind)
    | exact superpose eq4012 eq15
    | (have j1 := eq4012 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4063 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X1 X0
       have i₂ := eq4012 X0 (σ X1)
       grind)
    | exact superpose eq4012 eq75
    | (have j1 := eq4012 X0 (σ X1)
       grind)
    | exact resolve eq75 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq4067 : ∀ X0 : G, (M.op X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 ∨ (M.op X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq149 X0
       have i₂ := eq4012 X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))
       grind)
    | exact superpose eq4012 eq149
    | (have j1 := eq4012 X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))
       grind)
    | exact resolve eq149 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq4068 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq4012 X0 (τ X1)
       grind)
    | exact superpose eq4012 eq19
    | (have j1 := eq4012 X0 (τ X1)
       grind)
    | exact resolve eq19 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4070 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq4012 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq4012 eq89
    | (have j1 := eq4012 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq89 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq4075 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq4070 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4070
  have eq4076 : ∀ X0 : G, (M.op X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have j0 := eq4067 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4067
  have eq4191 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X0
       have i₂ := eq56 X0 X1
       grind)
    | (have i₁ := eq25 X0 X1
       have i₂ := eq56 X0 (M.op X1 X0)
       grind)
    | exact superpose eq56 eq25
    | (have j1 := eq56 X1 X0
       grind)
    | exact resolve eq25 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq4232 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4191
  have eq4240 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4075 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4075
    | exact resolve eq4075 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4075
  have eq4642 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq184 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq4695 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (τ X0) (τ (M.op X0 X0))
       have i₂ := eq4240 X0
       grind)
    | exact superpose eq4240 eq23
    | exact resolve eq23 eq4240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4240
  have eq5233 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4232 (σ X1) (σ X0)
       grind)
    | exact superpose eq4232 eq15
    | (have j1 := eq4232 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq4232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4232
  have eq5664 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (σ (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq4076 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4076
    | exact resolve eq4076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4076
  have eq6944 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op X1 (σ (σ (M.op (τ X0) (τ X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ (σ (M.op (τ X0) (τ X0)))) X1 (σ X0)
       have i₂ := eq5664 X0
       grind)
    | exact superpose eq5664 eq27
    | exact resolve eq27 eq5664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5664
  have eq20894 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4642 X1 (M.op X0 X1)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq4642
    | (have j0 := eq4642 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq4642 X0 (M.op X1 X0)
       have r₂ := eq25 X0 X1
       grind)
    | exact resolve eq4642 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4642
  have eq21021 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq20894 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20894
  have eq75382 : ∀ X0 X1 : G, (k (M.op X1 X0) X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X1 X1
       have i₂ := eq3647 X0 X1
       grind)
    | exact superpose eq3647 eq27
    | (have j1 := eq3647 X0 X1
       grind)
    | exact resolve eq27 eq3647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq75505 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ (M.op X1 X0))) ∨ (k (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4695 (M.op X1 X0)
       have i₂ := eq3647 X0 X1
       grind)
    | exact superpose eq3647 eq4695
    | (have j1 := eq3647 X0 X1
       grind)
    | exact resolve eq4695 eq3647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3647 eq4695
  have eq77029 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X1 (σ X0)) X0
       have i₂ := eq75382 (σ X0) X1
       grind)
    | exact superpose eq75382 eq67
    | (have j1 := eq75382 (σ X0) X1
       grind)
    | exact resolve eq67 eq75382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75382
  have eq77061 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77029 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq77029
    | (have j0 := eq77029 X0 X1
       grind)
    | exact resolve eq77029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77029
  have eq80502 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (M.op X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4012 X0 (τ (M.op X1 (σ X0)))
       have i₂ := eq77061 X0 X1
       grind)
    | exact superpose eq77061 eq4012
    | (have j0 := eq4012 X0 (τ (M.op X1 (σ X0)))
       have j1 := eq77061 X0 X1
       grind)
    | exact resolve eq4012 eq77061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4012 eq77061
  have eq80521 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq80502 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80502
  have eq225382 : ∀ X0 X1 : G, (M.op X0 (k X0 (τ X1))) = X0 ∨ (M.op X1 (σ X0)) = X1 ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80521 X0 X1
       have i₂ := eq4063 X1 X0
       grind)
    | exact superpose eq4063 eq80521
    | (have j0 := eq80521 X0 X1
       have j1 := eq4063 X1 X0
       grind)
    | exact resolve eq80521 eq4063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4063 eq80521
  have eq225399 : ∀ X0 X1 : G, (M.op X0 (k X0 (τ X1))) = X0 ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq225382 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225382
  have eq232362 : ∀ X0 X1 : G, (M.op X1 (k X1 X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq225399 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq225399
    | (have j0 := eq225399 X1 (σ X0)
       grind)
    | exact resolve eq225399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225399
  have eq248336 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq232362 x y
       grind)
    | exact superpose eq232362 eq16
    | (have j1 := eq232362 x y
       grind)
    | exact resolve eq16 eq232362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232362
  have eq281779 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4068 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4068
    | exact resolve eq4068 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4068
  have eq281840 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq281779 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq281779
    | (have j0 := eq281779 X0 X1
       grind)
    | exact resolve eq281779 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281779
  have eq1249085 : ∀ X0 X1 : G, (σ X0) = (k (M.op X1 (σ X0)) (σ X0)) ∨ (M.op X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75505 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75505
    | (have j0 := eq75505 (σ X0) X1
       grind)
    | exact resolve eq75505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75505
  have eq1957028 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4060 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4060
  have eq1957053 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1957028 (τ X1) (τ X0)
       have i₂ := eq79 X1 X0
       grind)
    | exact superpose eq79 eq1957028
    | (have j0 := eq1957028 (τ X1) (τ X0)
       grind)
    | exact resolve eq1957028 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1957097 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1957053 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1957053
    | (have j0 := eq1957053 X0 X1
       grind)
    | exact resolve eq1957053 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957053
  have eq1957100 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1957097 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1957097
    | (have j0 := eq1957097 X0 X1
       grind)
    | exact resolve eq1957097 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957097
  have eq1957101 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1957100 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1957100
    | (have j0 := eq1957100 X0 X1
       grind)
    | exact resolve eq1957100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957100
  have eq1957102 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1957101 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1957101
    | (have j0 := eq1957101 X0 X1
       grind)
    | exact resolve eq1957101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957101
  have eq1981916 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) ∨ (M.op X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X1 (σ X0)) X0
       have i₂ := eq1249085 X0 X1
       grind)
    | exact superpose eq1249085 eq67
    | (have j1 := eq1249085 X0 X1
       grind)
    | exact resolve eq67 eq1249085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq1249085
  have eq1981917 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 ∨ (M.op X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1981916 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1981916
    | (have j0 := eq1981916 X0 X1
       grind)
    | exact resolve eq1981916 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981916
  have eq1981920 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1981917 X0 X1
       have j1 := eq1957102 (τ (M.op X1 (σ X0))) X0
       grind)
    | (have r₁ := eq1981917 X1 X1
       have r₂ := eq1957102 (τ (M.op X1 (σ X1))) X1
       grind)
    | exact resolve eq1981917 eq1957102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957102 eq1981917
  have eq1982027 : ∀ X0 X1 : G, (M.op X1 (τ (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1981920 X1 (σ X0)
       have i₂ := eq5233 X1 X0
       grind)
    | exact superpose eq5233 eq1981920
    | (have j1 := eq5233 X1 X0
       grind)
    | exact resolve eq1981920 eq5233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5233
  have eq1982484 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1982027 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1982027
    | (have j0 := eq1982027 X0 X1
       grind)
    | exact resolve eq1982027 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982027
  have eq1990782 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1982484 y x
       grind)
    | exact superpose eq1982484 eq16
    | (have j1 := eq1982484 y x
       grind)
    | exact resolve eq16 eq1982484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982484
  have eq1990847 : x = (M.op x y) := by
    first
    | (have j1 := eq281840 y x
       grind)
    | (have r₁ := eq1990782
       have r₂ := eq281840 y x
       grind)
    | exact resolve eq1990782 eq281840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281840 eq1990782
  have eq1990891 : (σ x) ≠ (σ x) ∨ y = (M.op y (k y x)) := by
    first
    | (have i₁ := eq248336
       have i₂ := eq1990847
       grind)
    | exact superpose eq1990847 eq248336
    | exact resolve eq248336 eq1990847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248336
  have eq1991003 : y = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq21021 x y
       have i₂ := eq1990847
       grind)
    | exact superpose eq1990847 eq21021
    | exact resolve eq21021 eq1990847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21021
  have eq1991168 : y = (M.op y (k y x)) := by grind
  clear eq1990891
  have eq1991674 : ∀ X0 : G, (M.op X0 (M.op (k y x) (M.op X0 y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (k y x) y
       have i₂ := eq1991168
       grind)
    | exact superpose eq1991168 eq9
    | exact resolve eq9 eq1991168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991168
  have eq1996596 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1991674 X0
       have i₂ := eq1991003
       grind)
    | exact superpose eq1991003 eq1991674
    | exact resolve eq1991674 eq1991003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991003 eq1991674
  have eq1996746 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1996596 X0
       have i₂ := eq23 X0 y
       grind)
    | exact superpose eq23 eq1996596
    | exact resolve eq1996596 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996596
  have eq1996758 : ∀ X0 : G, y = (M.op y X0) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq23 X0 y
       have i₂ := eq1996746 X0
       grind)
    | exact superpose eq1996746 eq23
    | exact resolve eq23 eq1996746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996746
  have eq1997222 : ∀ X0 : G, (M.op X0 (τ y)) = X0 ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1981920 X0 y
       have i₂ := eq1996758 (σ X0)
       grind)
    | exact superpose eq1996758 eq1981920
    | exact resolve eq1981920 eq1996758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981920 eq1996758
  have eq1997725 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op X0 (σ (σ (τ y)))))) = X0 ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq6944 y X0
       have i₂ := eq1997222 (τ y)
       grind)
    | exact superpose eq1997222 eq6944
    | exact resolve eq6944 eq1997222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6944 eq1997222
  have eq1997794 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op X0 (σ y)))) = X0 ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1997725 X0
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq1997725
    | exact resolve eq1997725 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997725
  have eq1997825 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1997794 X0
       have i₂ := eq23 X0 (σ y)
       grind)
    | exact superpose eq23 eq1997794
    | exact resolve eq1997794 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1997794
  have eq1997993 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1997825 (σ x)
       grind)
    | exact superpose eq1997825 eq16
    | exact resolve eq16 eq1997825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997825
  have eq1998002 : (σ x) ≠ (σ x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq1997993
       have i₂ := eq1990847
       grind)
    | exact superpose eq1990847 eq1997993
    | exact resolve eq1997993 eq1990847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997993
  have eq1998003 : x = (k y x) := by grind
  clear eq1998002
  have eq1998199 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1957028 x y
       have i₂ := eq1998003
       grind)
    | exact superpose eq1998003 eq1957028
    | (have j0 := eq1957028 x y
       grind)
    | exact resolve eq1957028 eq1998003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957028 eq1998003
  have eq1998242 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1998199
  have eq1998469 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1998242
       grind)
    | exact superpose eq1998242 eq16
    | exact resolve eq16 eq1998242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998242
  have eq1998643 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1998469
       have i₂ := eq1990847
       grind)
    | exact superpose eq1990847 eq1998469
    | exact resolve eq1998469 eq1990847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990847 eq1998469
  have eq1998644 : False := by grind
  exact eq1998644

/-- `Equation433`: `x = x ◇ (y ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if X = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_y_y_pxy_Equation433 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law433 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law433.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X3 X2))) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X2 (M.op X0 (M.op X3 X2))) X0
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (M.op X1 X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq31
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X0) X0
       have i₂ := eq31 X2 X0
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq39 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
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
  have eq40 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq42 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X0))) = X1 ∨ (M.op X0 X2) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X2
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X2 X1) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq33
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq33 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq53 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq55 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq64 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53
    | exact resolve eq53 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq68 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq77 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68
    | exact resolve eq68 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq125 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X2 (M.op X0 (M.op X3 X2)))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29 (M.op X2 (M.op X0 (M.op X3 X2))) X1 X0 X0
       have i₂ := eq29 X0 X0 X2 X3
       grind)
    | exact superpose eq29 eq29
    | exact resolve eq29 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op X2 (M.op X3 (M.op X4 X2))) (M.op X0 X3)) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X1 (M.op (M.op X2 (M.op X3 (M.op X4 X2))) (M.op X0 X3)) X0
       have i₂ := eq29 X3 X0 X2 X4
       grind)
    | exact superpose eq29 eq9
    | exact resolve eq9 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq146 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq40
    | (have j0 := eq40 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq40 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq211 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X2 (M.op X1 X2)) = (k X2 (M.op X1 X2)) ∨ (M.op X1 X2) = X2 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X2)) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X2 X1 (M.op X1 X2)
       have i₂ := eq14 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq42 X0 X1 X2
       have i₂ := eq14 (M.op X2 (M.op X1 X0)) X1
       grind)
    | exact superpose eq14 eq42
    | (have j0 := eq42 X2 X1 (M.op X1 X2)
       have j1 := eq14 X2 (M.op X1 X2)
       grind)
    | exact resolve eq42 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq222 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X2)) ∨ (k X2 (M.op X1 X2)) = X2 ∨ (M.op X1 X2) = X2 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq211 X0 X1 X2
       have i₂ := eq31 X1 X2
       grind)
    | exact superpose eq31 eq211
    | (have j0 := eq211 X0 X1 X2
       grind)
    | exact resolve eq211 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq333 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X1) (M.op X2 (σ (k X0 X1))))) = X2 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X1) (σ X0)
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq9
    | (have j1 := eq38 X0 X1
       grind)
    | exact resolve eq9 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X1)
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq31
    | (have j1 := eq38 X0 X1
       grind)
    | exact resolve eq31 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1263 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X1 (M.op X2 (M.op X1 (M.op (M.op (M.op (M.op X3 (M.op X4 (M.op X5 X3))) (M.op X6 X4)) (M.op X0 X6)) (M.op X2 X0))))) = X1 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq125 X2 X1 (M.op (M.op (M.op X3 (M.op X4 (M.op X5 X3))) (M.op X6 X4)) (M.op X0 X6)) X0
       have i₂ := eq137 X6 X0 X3 X4 X5
       grind)
    | exact superpose eq137 eq125
    | exact resolve eq125 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq137
  have eq1498 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq39
    | exact resolve eq39 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1536 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (σ (M.op X0 X0)) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq11
    | (have j1 := eq39 X1 X0
       grind)
    | exact resolve eq11 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1625 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1498 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1498
    | (have j0 := eq1498 X0 X1
       grind)
    | exact resolve eq1498 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq2140 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1
       have i₂ := eq55 X0 X1
       grind)
    | (have i₁ := eq64 X0
       have i₂ := eq55 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq55 eq64
    | (have j1 := eq55 X0 X1
       grind)
    | exact resolve eq64 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq64
  have eq2432 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq146 x y
       grind)
    | exact superpose eq146 eq16
    | (have j1 := eq146 x y
       grind)
    | exact resolve eq16 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq3823 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) (σ X1)
       have i₂ := eq355 X0 X1
       grind)
    | exact superpose eq355 eq31
    | (have j1 := eq355 X0 X1
       grind)
    | exact resolve eq31 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq4373 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op X1 (σ X0)))) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    grind
  clear eq333
  have eq4481 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4373 X0 X1
       have i₂ := eq31 X1 (σ X0)
       grind)
    | exact superpose eq31 eq4373
    | (have j0 := eq4373 X0 X1
       grind)
    | exact resolve eq4373 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4373
  have eq16574 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq222 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq16575 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq16574 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16574
  have eq16637 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq16575 X0 X1
       grind)
    | (have r₁ := eq16575 X1 X0
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq16575 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16575
  have eq41492 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (σ (M.op X1 X1)) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq1536 X1 X0
       grind)
    | exact superpose eq1536 eq10
    | (have j1 := eq1536 X1 X0
       grind)
    | exact resolve eq10 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq41750 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (σ (M.op X1 X1)) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41492 X0 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq41492
    | (have j0 := eq41492 X0 X1
       grind)
    | exact resolve eq41492 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq41492
  have eq41780 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41750 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41750
    | (have j0 := eq41750 (σ X0) X1
       grind)
    | exact resolve eq41750 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41750
  have eq43053 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2140 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2140
    | (have j0 := eq2140 X1 (σ X0)
       grind)
    | exact resolve eq2140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2140
  have eq43254 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43053 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq43053
    | (have j0 := eq43053 X0 X1
       grind)
    | exact resolve eq43053 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43053
  have eq43258 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43254 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq43254
    | (have j0 := eq43254 X0 X1
       grind)
    | exact resolve eq43254 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43254
  have eq44790 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43258 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47456 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2432
       have i₂ := eq1625 x y
       grind)
    | exact superpose eq1625 eq2432
    | (have j1 := eq1625 x y
       grind)
    | (have r₁ := eq2432
       have r₂ := eq1625 x y
       grind)
    | (have r₁ := eq2432
       have r₂ := eq1625 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2432
       have r₂ := eq1625 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2432 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq47463 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq2432
       have i₂ := eq43258 y x
       grind)
    | exact superpose eq43258 eq2432
    | (have j1 := eq43258 y x
       grind)
    | (have r₁ := eq2432
       have r₂ := eq43258 y x
       grind)
    | (have r₁ := eq2432
       have r₂ := eq43258 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2432
       have r₂ := eq43258 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2432 eq43258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2432 eq43258
  have eq47467 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = y := by grind
  clear eq47463
  have eq47474 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq47456
  have eq47481 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq44790 x y
       grind)
    | (have r₁ := eq47467
       have r₂ := eq44790 x y
       grind)
    | exact resolve eq47467 eq44790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44790 eq47467
  have eq47514 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq47481
       grind)
    | exact superpose eq47481 eq10
    | exact resolve eq10 eq47481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47481
  have eq47664 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq47514
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq47514
    | exact resolve eq47514 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47514
  have eq47904 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq47 x y
       have i₂ := eq47664
       grind)
    | exact superpose eq47664 eq47
    | (have j0 := eq47 x y
       grind)
    | exact resolve eq47 eq47664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq47664
  have eq47951 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq47904
  have eq51163 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq35 y X0 x
       have i₂ := eq47951
       grind)
    | exact superpose eq47951 eq35
    | exact resolve eq35 eq47951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47951
  have eq51291 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 y) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq51163 X0
       have i₂ := eq31 X0 y
       grind)
    | exact superpose eq31 eq51163
    | exact resolve eq51163 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51163
  have eq57505 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j0 := eq51291 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51291
  have eq57506 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq57505
  have eq95162 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq47474
       have i₂ := eq57506
       grind)
    | exact superpose eq57506 eq47474
    | exact resolve eq47474 eq57506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47474
  have eq95190 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq95162
  have eq95389 : y = (k y x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16637 y y
       have i₂ := eq95190
       grind)
    | exact superpose eq95190 eq16637
    | exact resolve eq16637 eq95190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16637 eq95190
  have eq95392 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq95389
  have eq95487 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3823 y x
       have i₂ := eq95392
       grind)
    | exact superpose eq95392 eq3823
    | (have j0 := eq3823 y x
       grind)
    | exact resolve eq3823 eq95392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3823 eq95392
  have eq95544 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq95487
  have eq96445 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq95544
       grind)
    | exact superpose eq95544 eq16
    | exact resolve eq16 eq95544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95544
  have eq96576 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96445
       have i₂ := eq57506
       grind)
    | exact superpose eq57506 eq96445
    | exact resolve eq96445 eq57506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57506 eq96445
  have eq96589 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq96576
  have eq96590 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq96589
  have eq96596 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq96590
       grind)
    | exact superpose eq96590 eq10
    | exact resolve eq10 eq96590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96590
  have eq96744 : x = y ∨ x = y := by
    first
    | (have i₁ := eq96596
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq96596
    | exact resolve eq96596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96596
  have eq96745 : x = y := by grind
  clear eq96744
  have eq96749 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96745
       grind)
    | exact superpose eq96745 eq16
    | exact resolve eq16 eq96745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96745
  have eq96773 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = X0 ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq96749
       have i₂ := eq4481 x X0
       grind)
    | exact superpose eq4481 eq96749
    | (have j1 := eq4481 x X0
       grind)
    | (have r₁ := eq96749
       have r₂ := eq4481 x x
       grind)
    | exact resolve eq96749 eq4481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4481
  have eq96775 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq96749
       have i₂ := eq14 X0 (σ x)
       grind)
    | (have i₁ := eq96749
       have i₂ := eq14 (M.op (σ x) (σ x)) x
       grind)
    | exact superpose eq14 eq96749
    | (have j1 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq96749
       have r₂ := eq14 (σ (M.op x x)) (σ x)
       grind)
    | (have r₁ := eq96749
       have r₂ := eq14 (M.op (σ x) (σ x)) (σ (M.op x x))
       grind)
    | (have r₁ := eq96749
       have r₂ := eq14 (σ (M.op x x)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq96749 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96776 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq96773 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96773
  have eq98001 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (σ x)
       have i₂ := eq96776 X0
       grind)
    | exact superpose eq96776 eq31
    | exact resolve eq31 eq96776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98125 : ∀ X0 : G, (M.op x x) = (τ (σ x)) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq96776 X0
       grind)
    | exact superpose eq96776 eq10
    | (have j1 := eq96776 X0
       grind)
    | exact resolve eq10 eq96776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98209 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq98125 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq98125
    | (have j0 := eq98125 X0
       grind)
    | exact resolve eq98125 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98125
  have eq98445 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq96749
       have i₂ := eq98209 (σ x)
       grind)
    | exact superpose eq98209 eq96749
    | exact resolve eq96749 eq98209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98960 : ∀ X0 : G, (σ X0) ≠ (σ x) ∨ x = (M.op x x) ∨ (k X0 x) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq98445
       have i₂ := eq41780 X0 x
       grind)
    | (have i₁ := eq98445
       have i₂ := eq41780 (M.op x x) x
       grind)
    | exact superpose eq41780 eq98445
    | (have j1 := eq41780 X0 x
       grind)
    | (have r₁ := eq98445
       have r₂ := eq41780 x x
       grind)
    | (have r₁ := eq98445
       have r₂ := eq41780 (σ x) (σ (M.op x x))
       grind)
    | (have r₁ := eq98445
       have r₂ := eq41780 (σ (M.op x x)) (σ x)
       grind)
    | exact resolve eq98445 eq41780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98964 : ∀ X0 : G, (σ X0) ≠ (σ x) ∨ (k X0 x) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq98960 X0
       have j1 := eq44 X0 x
       grind)
    | (have r₁ := eq98960 X0
       have r₂ := eq44 (σ X0) (σ x)
       grind)
    | (have r₁ := eq98960 X0
       have r₂ := eq44 (σ x) (σ X0)
       grind)
    | (have r₁ := eq98960 X0
       have r₂ := eq44 X0 x
       grind)
    | exact resolve eq98960 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq98960
  have eq99311 : ∀ X0 X1 : G, (σ X0) = (σ x) ∨ (k X0 x) = (M.op X0 x) ∨ x = X0 ∨ (σ x) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41780 X0 x
       have i₂ := eq98001 X1
       grind)
    | exact superpose eq98001 eq41780
    | (have j0 := eq41780 X0 x
       have j1 := eq98001 X1
       grind)
    | exact resolve eq41780 eq98001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41780 eq98001
  have eq99391 : ∀ X0 X1 : G, (k X0 x) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) X1) ∨ x = X0 := by
    intro X0 X1
    first
    | (have j0 := eq99311 X0 X1
       have j1 := eq98964 X0
       grind)
    | (have r₁ := eq99311 X0 X1
       have r₂ := eq98964 X0
       grind)
    | (have r₁ := eq99311 x X1
       have r₂ := eq98964 x
       grind)
    | exact resolve eq99311 eq98964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98964 eq99311
  have eq103752 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (k X0 x) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq96749
       have i₂ := eq99391 X0 (σ x)
       grind)
    | exact superpose eq99391 eq96749
    | (have j1 := eq99391 X0 x
       grind)
    | exact resolve eq96749 eq99391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103869 : ∀ X0 X6 : G, (k X6 x) = (M.op X6 x) ∨ (M.op X0 (σ x)) = X0 ∨ x = X6 := by
    intro X0 X6
    first
    | (have i₁ := eq1263 x X0 (σ x) x x x x
       have i₂ := eq99391 X6 (M.op X0 (M.op (M.op (M.op (M.op x (M.op x (M.op x x))) (M.op x x)) (M.op x x)) (M.op (σ x) x)))
       grind)
    | exact superpose eq99391 eq1263
    | (have j1 := eq99391 X6 x
       grind)
    | exact resolve eq1263 eq99391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263 eq99391
  have eq113294 : (M.op (σ (M.op x x)) (σ x)) = (k (σ (M.op x x)) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have j0 := eq96775 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96775
  have eq113295 : (M.op (σ (M.op x x)) (σ x)) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq113294
       have i₂ := eq15 (M.op x x) x
       grind)
    | exact superpose eq15 eq113294
    | exact resolve eq113294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113294
  have eq113296 : (σ x) = (M.op (σ (M.op x x)) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq113295
  have eq113325 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq96776 (σ (M.op x x))
       have i₂ := eq113296
       grind)
    | exact superpose eq113296 eq96776
    | exact resolve eq96776 eq113296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96776
  have eq113331 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq98209 (σ (M.op x x))
       have i₂ := eq113296
       grind)
    | exact superpose eq113296 eq98209
    | exact resolve eq98209 eq113296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98209
  have eq113341 : ∀ X0 : G, (σ x) = (σ (M.op x x)) ∨ (k X0 x) = (M.op X0 x) ∨ x = X0 ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq103869 (σ (M.op x x)) X0
       have i₂ := eq113296
       grind)
    | exact superpose eq113296 eq103869
    | (have j0 := eq103869 X0 X0
       grind)
    | exact resolve eq103869 eq113296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103869 eq113296
  have eq113397 : ∀ X0 : G, (σ x) = (σ (M.op x x)) ∨ (k X0 x) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq113341 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113341
  have eq113406 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq113331
  have eq113412 : (σ x) = (σ (M.op x x)) := by grind
  clear eq113325
  have eq113454 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq113397 X0
       have j1 := eq103752 X0
       grind)
    | (have r₁ := eq113397 X0
       have r₂ := eq103752 X0
       grind)
    | exact resolve eq113397 eq103752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103752 eq113397
  have eq113456 : x = (M.op x x) := by
    first
    | (have r₁ := eq113406
       have r₂ := eq98445
       grind)
    | exact resolve eq113406 eq98445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98445 eq113406
  have eq113510 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq35 x X0 x
       have i₂ := eq113456
       grind)
    | exact superpose eq113456 eq35
    | exact resolve eq35 eq113456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq113456
  have eq113779 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq113510 X0
       have i₂ := eq31 X0 x
       grind)
    | exact superpose eq31 eq113510
    | exact resolve eq113510 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq113510
  have eq117827 : x = (M.op (τ (M.op (σ x) (σ x))) x) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq77 x
       have i₂ := eq113454 (τ (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq113454 eq77
    | (have j1 := eq113454 (M.op (τ (M.op (σ x) (σ x))) x)
       grind)
    | exact resolve eq77 eq113454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq113454
  have eq117942 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq117827
       have i₂ := eq113779 (τ (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq113779 eq117827
    | exact resolve eq117827 eq113779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113779 eq117827
  have eq117943 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq117942
  have eq118122 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ x))
       have i₂ := eq117943
       grind)
    | exact superpose eq117943 eq11
    | exact resolve eq11 eq117943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117943
  have eq118362 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq96749
       have i₂ := eq118122
       grind)
    | exact superpose eq118122 eq96749
    | exact resolve eq96749 eq118122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96749 eq118122
  have eq118697 : False := by grind
  exact eq118697

/-- `Equation433`: `x = x ◇ (y ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_x_pyx_pxy_Equation433 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law433 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law433.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X0) X0
       have i₂ := eq25 X2 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq35 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X2 X0)) ∨ (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X2) X2 X1
       have i₂ := eq14 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X2 X1))
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 (M.op X1 X2) X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq52 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq27 (τ X0) (τ X0)
       grind)
    | exact superpose eq27 eq49
    | (have j0 := eq49 X0
       grind)
    | exact resolve eq49 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq57 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq66 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52
    | exact resolve eq52 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq62
  have eq114 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq27 (σ X0) (σ X0)
       grind)
    | exact superpose eq27 eq106
    | (have j0 := eq106 X0
       grind)
    | exact resolve eq106 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq177 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X2)) = (M.op (M.op (M.op X1 X2) (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       have i₂ := eq29 X2 X0 X1
       grind)
    | exact superpose eq29 eq25
    | exact resolve eq25 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32 x y
       grind)
    | exact superpose eq32 eq16
    | (have j1 := eq32 x y
       grind)
    | exact resolve eq16 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X0) (σ X1)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq25
    | (have j1 := eq32 X0 X1
       grind)
    | exact resolve eq25 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X2
       have i₂ := eq32 X0 X2
       grind)
    | exact superpose eq32 eq15
    | (have j1 := eq32 X0 X2
       grind)
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq421 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X0 X1)) ∨ (k (M.op X0 X1) X2) = (M.op (M.op X0 X1) X2) ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq35 X2 X0 X1
       grind)
    | exact superpose eq35 eq25
    | (have j1 := eq35 X2 X0 X1
       grind)
    | exact resolve eq25 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1
       have i₂ := eq35 X0 X0 X0
       grind)
    | exact superpose eq35 eq14
    | (have j0 := eq14 (M.op X0 X0) X1
       have j1 := eq35 X1 X0 X0
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq428 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq427 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq432 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq428 X0 X1
       have i₂ := eq27 X0 X0
       grind)
    | exact superpose eq27 eq428
    | (have j0 := eq428 X0 X1
       grind)
    | exact resolve eq428 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq1081 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq57
    | exact resolve eq57 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1145 : ∀ X0 X1 X2 : G, (k (σ X1) X2) = (σ (k X1 (M.op X0 X0))) ∨ (k (σ X0) X2) = (σ (M.op X0 (τ X2))) ∨ (τ X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X2 X1
       have i₂ := eq57 X0 X2
       grind)
    | exact superpose eq57 eq20
    | (have j1 := eq57 X0 X2
       grind)
    | exact resolve eq20 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq57
  have eq1174 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1081 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1081
    | (have j0 := eq1081 X0 X1
       grind)
    | exact resolve eq1081 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1454 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq304
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq304
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq304
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq304
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq304 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq1464 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq1454
  have eq1546 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1174 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1575 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
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
  have eq1647 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1575 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq1575
    | (have j0 := eq1575 X0
       grind)
    | exact resolve eq1575 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575
  have eq2948 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq308 (τ X0) (τ X1)
       have i₂ := eq66 X1 X0
       grind)
    | exact superpose eq66 eq308
    | (have j0 := eq308 (τ X0) (τ X1)
       grind)
    | exact resolve eq308 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3084 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X1 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) (σ X0)
       have i₂ := eq308 X0 X1
       grind)
    | exact superpose eq308 eq27
    | (have j1 := eq308 X1 X0
       grind)
    | exact resolve eq27 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq3124 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2948 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2948
    | (have j0 := eq2948 X0 X1
       grind)
    | exact resolve eq2948 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2948
  have eq3132 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3124 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3124
    | (have j0 := eq3124 X0 X1
       grind)
    | exact resolve eq3124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3124
  have eq3135 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X1 (k X0 X1)) = X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3132 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3132
    | (have j0 := eq3132 X0 X1
       grind)
    | exact resolve eq3132 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3132
  have eq3136 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 (k X0 X1)) = X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3135 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3135
    | (have j0 := eq3135 X0 X1
       grind)
    | exact resolve eq3135 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135
  have eq3137 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3136 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3136
    | (have j0 := eq3136 X0 X1
       grind)
    | exact resolve eq3136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3136
  have eq3138 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3137 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3137
    | (have j0 := eq3137 X0 X1
       grind)
    | exact resolve eq3137 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3137
  have eq3169 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (k X2 X0)))) = X1 ∨ (M.op X2 X2) = X0 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (k X2 X0) X1 X0
       have i₂ := eq3138 X2 X0
       grind)
    | exact superpose eq3138 eq29
    | (have j1 := eq3138 X2 X0
       grind)
    | exact resolve eq29 eq3138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3138
  have eq5838 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1 X1
       have i₂ := eq421 X0 X1 X1
       grind)
    | exact superpose eq421 eq177
    | (have j1 := eq421 X1 X0 X0
       grind)
    | exact resolve eq177 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq5944 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5838 X0 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq5838
    | (have j0 := eq5838 X0 X1
       grind)
    | exact resolve eq5838 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5838
  have eq7038 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq315 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq315
    | exact resolve eq315 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq7242 : ∀ X0 X1 X2 : G, (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7038 X0 X1 X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq7038
    | (have j0 := eq7038 X0 X1 X2
       grind)
    | exact resolve eq7038 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq7038
  have eq10055 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq432 X0 (k (M.op X0 X0) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq10056 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10055 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10055
  have eq10122 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10056 X0
       have j1 := eq5944 X0 X0
       grind)
    | (have r₁ := eq10056 x
       have r₂ := eq5944 x x
       grind)
    | exact resolve eq10056 eq5944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5944 eq10056
  have eq47470 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq114 x
       have i₂ := eq1464
       grind)
    | exact superpose eq1464 eq114
    | exact resolve eq114 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464
  have eq47634 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq47470
  have eq47709 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq47634
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq47634
    | exact resolve eq47634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47634
  have eq49906 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq47709
       grind)
    | exact superpose eq47709 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq47709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49928 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3169 y X0 x
       have i₂ := eq47709
       grind)
    | exact superpose eq47709 eq3169
    | (have j0 := eq3169 y x x
       grind)
    | exact resolve eq3169 eq47709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3169 eq47709
  have eq49969 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq49928 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49928
  have eq49991 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq49906
  have eq50004 : ∀ X0 : G, y = (M.op x x) ∨ (M.op X0 y) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq49969 X0
       have i₂ := eq25 X0 y
       grind)
    | exact superpose eq25 eq49969
    | exact resolve eq49969 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49969
  have eq52698 : x = y ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49991
       have i₂ := eq50004 x
       grind)
    | exact superpose eq50004 eq49991
    | exact resolve eq49991 eq50004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49991 eq50004
  have eq52699 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq52698
  have eq53615 : y = (k y x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10122 x
       have i₂ := eq52699
       grind)
    | exact superpose eq52699 eq10122
    | exact resolve eq10122 eq52699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53626 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25 x x
       have i₂ := eq52699
       grind)
    | exact superpose eq52699 eq25
    | exact resolve eq25 eq52699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52699
  have eq53724 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq53615
  have eq65456 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3084 X0 (M.op X0 X0)
       have i₂ := eq10122 X0
       grind)
    | exact superpose eq10122 eq3084
    | (have j0 := eq3084 X0 (M.op X0 X0)
       have j1 := eq10122 X0
       grind)
    | exact resolve eq3084 eq10122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10122
  have eq65486 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3084 x y
       have i₂ := eq53724
       grind)
    | exact superpose eq53724 eq3084
    | (have j0 := eq3084 x y
       grind)
    | exact resolve eq3084 eq53724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3084 eq53724
  have eq65699 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq65486
  have eq65709 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq65456 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65456
  have eq65825 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq65699
       grind)
    | exact superpose eq65699 eq16
    | exact resolve eq16 eq65699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65699
  have eq66100 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq65825
       have i₂ := eq53626
       grind)
    | exact superpose eq53626 eq65825
    | exact resolve eq65825 eq53626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53626 eq65825
  have eq66115 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq66100
  have eq66116 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq66115
  have eq66449 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq66116
       grind)
    | exact superpose eq66116 eq10
    | exact resolve eq10 eq66116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66116
  have eq66562 : x = y ∨ x = y := by
    first
    | (have i₁ := eq66449
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq66449
    | exact resolve eq66449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66449
  have eq66563 : x = y := by grind
  clear eq66562
  have eq67024 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66563
       grind)
    | exact superpose eq66563 eq16
    | exact resolve eq16 eq66563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66563
  have eq67530 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq67024
       have i₂ := eq14 (σ x) X0
       grind)
    | (have i₁ := eq67024
       have i₂ := eq14 X0 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq14 eq67024
    | (have j1 := eq14 (σ x) X0
       grind)
    | (have r₁ := eq67024
       have r₂ := eq14 (σ x) (σ (M.op x x))
       grind)
    | (have r₁ := eq67024
       have r₂ := eq14 (M.op (σ x) (σ x)) (σ (M.op x x))
       grind)
    | (have r₁ := eq67024
       have r₂ := eq14 (σ (M.op x x)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq67024 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69912 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) (M.op X2 X2)) ∨ (M.op X2 (σ (τ X1))) = (k X2 (σ (τ X1))) ∨ (σ (τ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7242 X2 (τ X1) (τ X0)
       have i₂ := eq66 X1 X0
       grind)
    | exact superpose eq66 eq7242
    | (have j0 := eq7242 X2 (τ X1) X2
       grind)
    | exact resolve eq7242 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq7242
  have eq70711 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (M.op X2 X2)) ∨ (M.op X2 (σ (τ X1))) = (k X2 (σ (τ X1))) ∨ (σ (τ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69912 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq69912
    | (have j0 := eq69912 X0 X1 X2
       grind)
    | exact resolve eq69912 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69912
  have eq70769 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (M.op X2 (σ (τ X1))) = (k X2 (σ (τ X1))) ∨ (σ (τ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70711 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq70711
    | (have j0 := eq70711 X0 X1 X2
       grind)
    | exact resolve eq70711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70711
  have eq70794 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (σ (τ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70769 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70769
    | (have j0 := eq70769 X0 X1 X2
       grind)
    | exact resolve eq70769 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70769
  have eq70804 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (M.op X2 X1) = (k X2 X1) ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70794 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq70794
    | (have j0 := eq70794 X0 X1 X2
       grind)
    | exact resolve eq70794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70794
  have eq81987 : ∀ X0 X1 X2 : G, (k (τ (σ X0)) X2) = (τ (σ (k X0 (M.op X1 X1)))) ∨ (k (σ X1) (σ X2)) = (σ (M.op X1 (τ (σ X2)))) ∨ (τ (σ X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (σ X0) X2
       have i₂ := eq1145 X1 X0 (σ X2)
       grind)
    | exact superpose eq1145 eq52
    | (have j1 := eq1145 X1 X1 (σ X2)
       grind)
    | exact resolve eq52 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1145
  have eq82424 : ∀ X0 X1 X2 : G, (k (τ (σ X0)) X2) = (k X0 (M.op X1 X1)) ∨ (k (σ X1) (σ X2)) = (σ (M.op X1 (τ (σ X2)))) ∨ (τ (σ X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81987 X0 X1 X2
       have i₂ := eq10 (k X0 (M.op X1 X1))
       grind)
    | exact superpose eq10 eq81987
    | (have j0 := eq81987 X0 X1 X2
       grind)
    | exact resolve eq81987 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81987
  have eq82511 : ∀ X0 X1 X2 : G, (k X0 X2) = (k X0 (M.op X1 X1)) ∨ (k (σ X1) (σ X2)) = (σ (M.op X1 (τ (σ X2)))) ∨ (τ (σ X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82424 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82424
    | (have j0 := eq82424 X0 X1 X2
       grind)
    | exact resolve eq82424 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82424
  have eq82553 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X2)) = (σ (M.op X1 X2)) ∨ (k X0 X2) = (k X0 (M.op X1 X1)) ∨ (τ (σ X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82511 X0 X1 X2
       have i₂ := eq10 X2
       grind)
    | exact superpose eq10 eq82511
    | (have j0 := eq82511 X0 X1 X2
       grind)
    | exact resolve eq82511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82511
  have eq82581 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (σ (M.op X1 X2)) ∨ (k X0 X2) = (k X0 (M.op X1 X1)) ∨ (τ (σ X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82553 X0 X1 X2
       have i₂ := eq15 X1 X2
       grind)
    | exact superpose eq15 eq82553
    | (have j0 := eq82553 X0 X1 X2
       grind)
    | exact resolve eq82553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82553
  have eq82595 : ∀ X0 X1 X2 : G, (k X0 X2) = (k X0 (M.op X1 X1)) ∨ (σ (k X1 X2)) = (σ (M.op X1 X2)) ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82581 X0 X1 X2
       have i₂ := eq10 X2
       grind)
    | exact superpose eq10 eq82581
    | (have j0 := eq82581 X0 X1 X2
       grind)
    | exact resolve eq82581 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82581
  have eq91501 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 (M.op X0 X0)) ∨ (k X0 X1) = (k X0 (M.op X0 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq70804 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70804
  have eq96871 : (k (σ x) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have j0 := eq67530 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67530
  have eq96872 : (σ (k x (M.op x x))) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq96871
       have i₂ := eq15 x (M.op x x)
       grind)
    | exact superpose eq15 eq96871
    | exact resolve eq96871 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96871
  have eq111453 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1647 X0
       have i₂ := eq82595 X0 X0 X1
       grind)
    | (have i₁ := eq1647 X0
       have i₂ := eq82595 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq82595 eq1647
    | (have j0 := eq1647 X0
       have j1 := eq82595 X0 X0 X1
       grind)
    | exact resolve eq1647 eq82595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82595
  have eq111535 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq111453 X0 X1
       have j1 := eq1546 X1 X0
       grind)
    | (have r₁ := eq111453 X1 X1
       have r₂ := eq1546 X0 X1
       grind)
    | (have r₁ := eq111453 (M.op X1 X1) X1
       have r₂ := eq1546 X0 X1
       grind)
    | (have r₁ := eq111453 X1 (M.op X1 X1)
       have r₂ := eq1546 X0 X1
       grind)
    | exact resolve eq111453 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546 eq111453
  have eq135686 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq111535 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111535
  have eq163633 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op X1 X0))) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq135686 X1 (M.op X0 X1)
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq135686
    | (have j0 := eq135686 (σ X0) (σ (k X0 (M.op X1 X0)))
       grind)
    | exact resolve eq135686 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135686
  have eq173170 : (σ x) = (σ (k x (M.op x x))) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq96872
       have i₂ := eq65709 x
       grind)
    | exact superpose eq65709 eq96872
    | (have j1 := eq65709 x
       grind)
    | exact resolve eq96872 eq65709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65709 eq96872
  have eq173176 : (σ x) = (σ (k x (M.op x x))) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq173170
  have eq173179 : (σ x) = (σ (k x (M.op x x))) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq163633 x x
       grind)
    | (have r₁ := eq173176
       have r₂ := eq163633 x x
       grind)
    | exact resolve eq173176 eq163633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163633 eq173176
  have eq173215 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1647 x
       have i₂ := eq173179
       grind)
    | exact superpose eq173179 eq1647
    | (have j0 := eq1647 x
       grind)
    | exact resolve eq1647 eq173179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647 eq173179
  have eq173296 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq173215
  have eq173371 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq173296
       grind)
    | exact superpose eq173296 eq10
    | exact resolve eq10 eq173296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173296
  have eq173460 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq173371
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq173371
    | exact resolve eq173371 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173371
  have eq173461 : x = (M.op x x) := by grind
  clear eq173460
  have eq173540 : ∀ X0 : G, (M.op x X0) ≠ (k x x) ∨ (k x X0) = (k x x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq91501 x x
       have i₂ := eq173461
       grind)
    | exact superpose eq173461 eq91501
    | (have j0 := eq91501 (k x X0) (k x x)
       grind)
    | exact resolve eq91501 eq173461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91501
  have eq173639 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq29 x X0 x
       have i₂ := eq173461
       grind)
    | exact superpose eq173461 eq29
    | exact resolve eq29 eq173461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq173672 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x (M.op X0 x)) X0) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x x
       have i₂ := eq173461
       grind)
    | exact superpose eq173461 eq177
    | exact resolve eq177 eq173461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq173461
  have eq173953 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq173672 X0
       have i₂ := eq25 X0 x
       grind)
    | exact superpose eq25 eq173672
    | exact resolve eq173672 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173672
  have eq173963 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq173639 X0
       have i₂ := eq25 X0 x
       grind)
    | exact superpose eq25 eq173639
    | exact resolve eq173639 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq173639
  have eq173969 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (k x X0) = (k x x) ∨ x = X0 := by
    intro X0
    grind
  clear eq173540
  have eq173977 : ∀ X0 : G, (k x X0) = (k x x) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq173969 X0
       grind)
    | (have r₁ := eq173969 X0
       have r₂ := eq173953 X0
       grind)
    | exact resolve eq173969 eq173953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173953 eq173969
  have eq173981 : ∀ X0 : G, x = (k x X0) ∨ x = X0 := by
    intro X0
    grind
  clear eq173977
  have eq176577 : x = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq114 x
       have i₂ := eq173981 (τ (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq173981 eq114
    | (have j0 := eq114 x
       have j1 := eq173981 (τ (M.op (σ x) (σ x)))
       grind)
    | exact resolve eq114 eq173981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq173981
  have eq176666 : x = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq176577
  have eq246314 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ x))
       have i₂ := eq176666
       grind)
    | exact superpose eq176666 eq11
    | exact resolve eq11 eq176666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176666
  have eq246346 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq246314
  have eq246400 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq67024
       have i₂ := eq246346
       grind)
    | exact superpose eq246346 eq67024
    | exact resolve eq67024 eq246346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67024 eq246346
  have eq246863 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq246400
       have i₂ := eq173963 x
       grind)
    | exact superpose eq173963 eq246400
    | exact resolve eq246400 eq173963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173963 eq246400
  have eq246864 : False := by grind
  exact eq246864

/-- `Equation433`: `x = x ◇ (y ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pyx_Equation433 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law433 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law433.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 (M.op X1 X0)
       have i₂ := eq26 X1 X0
       grind)
    | exact superpose eq26 eq26
    | exact resolve eq26 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X0) X0
       have i₂ := eq26 X2 X0
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq42 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq50 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq60 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq19
  have eq95 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq114 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq16
    | (have j1 := eq44 x y
       grind)
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X1) (σ X0)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq26
    | (have j1 := eq44 X1 X0
       grind)
    | exact resolve eq26 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X0) (M.op X2 (σ (k X0 X1))))) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq9
    | (have j1 := eq44 X1 X0
       grind)
    | exact resolve eq9 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq349 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 (M.op X1 (σ X0))
       have i₂ := eq42 X1 (σ X0)
       grind)
    | exact superpose eq42 eq60
    | (have j1 := eq42 X1 (σ X0)
       grind)
    | exact resolve eq60 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq60
  have eq354 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq349 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq349
    | (have j0 := eq349 X0 X1
       grind)
    | exact resolve eq349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq2062 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq114
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq114
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq114
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq114
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq114 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq2063 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2062
  have eq2413 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq119 (τ X0) (τ X1)
       have i₂ := eq95 X1 X0
       grind)
    | exact superpose eq95 eq119
    | (have j0 := eq119 (τ X0) (τ X1)
       grind)
    | exact resolve eq119 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq119
  have eq2459 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2413 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2413
    | (have j0 := eq2413 X0 X1
       grind)
    | exact resolve eq2413 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413
  have eq2473 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2459 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2459
    | (have j0 := eq2459 X0 X1
       grind)
    | exact resolve eq2459 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2459
  have eq2477 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2473 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2473
    | (have j0 := eq2473 X0 X1
       grind)
    | exact resolve eq2473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473
  have eq2479 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2477 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2477
    | (have j0 := eq2477 X0 X1
       grind)
    | exact resolve eq2477 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477
  have eq2481 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2479 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2479
    | (have j0 := eq2479 X0 X1
       grind)
    | exact resolve eq2479 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2483 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2481 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2481
    | (have j0 := eq2481 X0 X1
       grind)
    | exact resolve eq2481 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481
  have eq28363 : y = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq354 y (σ x)
       have i₂ := eq2063
       grind)
    | exact superpose eq2063 eq354
    | exact resolve eq354 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq2063
  have eq28445 : y = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq28363
  have eq28455 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq28445
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28445
    | exact resolve eq28445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28445
  have eq28460 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq28455
       have r₂ := eq13 y x
       grind)
    | exact resolve eq28455 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28455
  have eq28468 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op X0 (σ y)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq120 y x X0
       have i₂ := eq28460
       grind)
    | exact superpose eq28460 eq120
    | (have j0 := eq120 y x x
       grind)
    | exact resolve eq120 eq28460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq28473 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2483 y x
       have i₂ := eq28460
       grind)
    | exact superpose eq28460 eq2483
    | (have j0 := eq2483 y x
       grind)
    | exact resolve eq2483 eq28460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2483 eq28460
  have eq28474 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq28473
  have eq28479 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op X0 (σ y)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq28468 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28468
  have eq28487 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq28479 X0
       have i₂ := eq26 X0 (σ y)
       grind)
    | exact superpose eq26 eq28479
    | exact resolve eq28479 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28479
  have eq167147 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq30 y X0 y
       have i₂ := eq28474
       grind)
    | exact superpose eq28474 eq30
    | exact resolve eq30 eq28474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq28474
  have eq167168 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 y) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq167147 X0
       have i₂ := eq26 X0 y
       grind)
    | exact superpose eq26 eq167147
    | exact resolve eq167147 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq167147
  have eq179675 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j0 := eq167168 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167168
  have eq179676 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq179675
  have eq1004946 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq28487 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28487
  have eq1004947 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1004946
  have eq1005424 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1004947
       grind)
    | exact superpose eq1004947 eq16
    | exact resolve eq16 eq1004947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004947
  have eq1005934 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1005424
       have i₂ := eq179676
       grind)
    | exact superpose eq179676 eq1005424
    | exact resolve eq1005424 eq179676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179676 eq1005424
  have eq1005935 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1005934
  have eq1005936 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1005935
  have eq1006009 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1005936
       grind)
    | exact superpose eq1005936 eq10
    | exact resolve eq10 eq1005936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005936
  have eq1006351 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1006009
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1006009
    | exact resolve eq1006009 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006009
  have eq1006352 : x = y := by grind
  clear eq1006351
  have eq1006455 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1006352
       grind)
    | exact superpose eq1006352 eq16
    | exact resolve eq16 eq1006352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006352
  have eq1006456 : False := by grind
  exact eq1006456

/-- `Equation433`: `x = x ◇ (y ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_x_pyy_pyx_Equation433 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law433 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law433.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X0) X0
       have i₂ := eq25 X2 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq42 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X2 X0)) ∨ (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X0) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X2) X2 X1
       have i₂ := eq14 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X0 (M.op X2 X1)) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 (M.op X1 X2)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq45 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq51 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq56 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq65 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51
    | exact resolve eq51 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq51
  have eq130 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq45
    | (have j0 := eq45 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq45 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38 x y
       grind)
    | exact superpose eq38 eq16
    | (have j1 := eq38 x y
       grind)
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq25
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq25 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X2
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq15
    | (have j1 := eq38 X0 X1
       grind)
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq373 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0)
       have i₂ := eq42 X0 X0 X0
       grind)
    | exact superpose eq42 eq14
    | (have j0 := eq14 X1 (M.op X0 X0)
       have j1 := eq42 X1 X0 X0
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq374 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq373 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq378 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0 X1
       have i₂ := eq27 X0 X0
       grind)
    | exact superpose eq27 eq374
    | (have j0 := eq374 X0 X1
       grind)
    | exact resolve eq374 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq1443 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0)
       have i₂ := eq130 X0 X1
       grind)
    | exact superpose eq130 eq25
    | (have j1 := eq130 X0 X1
       grind)
    | exact resolve eq25 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq1541 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq255
       have i₂ := eq45 y x
       grind)
    | exact superpose eq45 eq255
    | (have j1 := eq45 (σ y) (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq255
       have r₂ := eq45 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq255
       have r₂ := eq45 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq255 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq255
  have eq1544 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y x) := by grind
  clear eq1541
  have eq1659 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56
    | exact resolve eq56 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1729 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1659 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq1659
    | (have j0 := eq1659 X0
       grind)
    | exact resolve eq1659 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659
  have eq2532 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq259 (τ X0) (τ X1)
       have i₂ := eq65 X1 X0
       grind)
    | exact superpose eq65 eq259
    | (have j0 := eq259 (τ X0) (τ X1)
       grind)
    | exact resolve eq259 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq2699 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2532 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2532
    | (have j0 := eq2532 X0 X1
       grind)
    | exact resolve eq2532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532
  have eq2706 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2699 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2699
    | (have j0 := eq2699 X0 X1
       grind)
    | exact resolve eq2699 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699
  have eq2709 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2706 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2706
    | (have j0 := eq2706 X0 X1
       grind)
    | exact resolve eq2706 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2706
  have eq2710 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2709 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2709
    | (have j0 := eq2709 X0 X1
       grind)
    | exact resolve eq2709 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2709
  have eq2711 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2710 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2710
    | (have j0 := eq2710 X0 X1
       grind)
    | exact resolve eq2710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2710
  have eq2712 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2711 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2711
    | (have j0 := eq2711 X0 X1
       grind)
    | exact resolve eq2711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711
  have eq2741 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (k X0 X2)))) = X1 ∨ (M.op X2 X2) = X0 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (k X0 X2) X1 X0
       have i₂ := eq2712 X0 X2
       grind)
    | exact superpose eq2712 eq29
    | (have j1 := eq2712 X0 X2
       grind)
    | exact resolve eq29 eq2712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2712
  have eq5509 : ∀ X0 X1 X2 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq266 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq266
    | exact resolve eq266 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq5673 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5509 X0 X1 X2
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq5509
    | (have j0 := eq5509 X0 X1 X2
       grind)
    | exact resolve eq5509 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5509
  have eq8917 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq378 X0 (k X0 (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq8918 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8917 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8917
  have eq8976 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8918 X0
       have i₂ := eq27 X0 X0
       grind)
    | exact superpose eq27 eq8918
    | (have j0 := eq8918 X0
       grind)
    | (have r₁ := eq8918 X0
       have r₂ := eq27 X0 X0
       grind)
    | exact resolve eq8918 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq8918
  have eq8977 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8976 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8976
  have eq46710 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1443 X0 (M.op X0 X0)
       have i₂ := eq8977 X0
       grind)
    | exact superpose eq8977 eq1443
    | (have j0 := eq1443 X0 (M.op X0 X0)
       have j1 := eq8977 X0
       grind)
    | exact resolve eq1443 eq8977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46949 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq46710 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46710
  have eq48334 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq71 x
       have i₂ := eq1544
       grind)
    | exact superpose eq1544 eq71
    | exact resolve eq71 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq48509 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y x) := by grind
  clear eq48334
  have eq48581 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq48509
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq48509
    | exact resolve eq48509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48509
  have eq48582 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq48581
  have eq48710 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq48582
       grind)
    | exact superpose eq48582 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq48582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48728 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2741 y X0 x
       have i₂ := eq48582
       grind)
    | exact superpose eq48582 eq2741
    | (have j0 := eq2741 y x x
       grind)
    | exact resolve eq2741 eq48582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2741 eq48582
  have eq48779 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq48728 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48728
  have eq48797 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq48710
  have eq48813 : ∀ X0 : G, y = (M.op x x) ∨ (M.op X0 y) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq48779 X0
       have i₂ := eq25 X0 y
       grind)
    | exact superpose eq25 eq48779
    | exact resolve eq48779 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48779
  have eq58400 : x = y ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48797
       have i₂ := eq48813 x
       grind)
    | exact superpose eq48813 eq48797
    | exact resolve eq48797 eq48813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48797 eq48813
  have eq58401 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq58400
  have eq59421 : y = (k x y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8977 x
       have i₂ := eq58401
       grind)
    | exact superpose eq58401 eq8977
    | exact resolve eq8977 eq58401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8977
  have eq59434 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25 x x
       have i₂ := eq58401
       grind)
    | exact superpose eq58401 eq25
    | exact resolve eq25 eq58401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58401
  have eq59555 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq59421
  have eq62466 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1443 x y
       have i₂ := eq59555
       grind)
    | exact superpose eq59555 eq1443
    | (have j0 := eq1443 x y
       grind)
    | exact resolve eq1443 eq59555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443 eq59555
  have eq62557 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq62466
  have eq65046 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq62557
       grind)
    | exact superpose eq62557 eq16
    | exact resolve eq16 eq62557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62557
  have eq65679 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq65046
       have i₂ := eq59434
       grind)
    | exact superpose eq59434 eq65046
    | exact resolve eq65046 eq59434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59434 eq65046
  have eq65694 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq65679
  have eq65695 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq65694
  have eq66193 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq65695
       grind)
    | exact superpose eq65695 eq10
    | exact resolve eq10 eq65695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65695
  have eq66302 : x = y ∨ x = y := by
    first
    | (have i₁ := eq66193
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq66193
    | exact resolve eq66193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66193
  have eq66303 : x = y := by grind
  clear eq66302
  have eq66842 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66303
       grind)
    | exact superpose eq66303 eq16
    | exact resolve eq16 eq66303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66303
  have eq67178 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq66842
       have i₂ := eq14 X0 (σ x)
       grind)
    | (have i₁ := eq66842
       have i₂ := eq14 (M.op (σ x) (σ x)) x
       grind)
    | exact superpose eq14 eq66842
    | (have j1 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq66842
       have r₂ := eq14 (σ (M.op x x)) (σ x)
       grind)
    | (have r₁ := eq66842
       have r₂ := eq14 (M.op (σ x) (σ x)) (σ (M.op x x))
       grind)
    | (have r₁ := eq66842
       have r₂ := eq14 (σ (M.op x x)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq66842 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67785 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) (σ (τ X1))) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5673 X2 (τ X0) (τ X1)
       have i₂ := eq65 X1 X0
       grind)
    | exact superpose eq65 eq5673
    | (have j0 := eq5673 X2 (τ X0) X2
       grind)
    | exact resolve eq5673 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq5673
  have eq68576 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) X1) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67785 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq67785
    | (have j0 := eq67785 X0 X1 X2
       grind)
    | exact resolve eq67785 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67785
  have eq68625 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68576 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq68576
    | (have j0 := eq68576 X0 X1 X2
       grind)
    | exact resolve eq68576 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68576
  have eq68644 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (k X0 X1) = (k (M.op X2 X2) X1) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68625 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq68625
    | (have j0 := eq68625 X0 X1 X2
       grind)
    | exact resolve eq68625 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68625
  have eq68653 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (M.op X2 X0) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68644 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq68644
    | (have j0 := eq68644 X0 X1 X2
       grind)
    | exact resolve eq68644 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68644
  have eq92207 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq68653 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68653
  have eq93542 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) ≠ X0 ∨ (k (M.op X1 X0) X0) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq92207 (M.op X0 X1) X1
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq92207
    | (have j0 := eq92207 (k (M.op X1 X0) X0) X0
       grind)
    | exact resolve eq92207 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92207
  have eq95507 : (k (σ (M.op x x)) (σ x)) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have j0 := eq67178 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67178
  have eq95508 : (σ (k (M.op x x) x)) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq95507
       have i₂ := eq15 (M.op x x) x
       grind)
    | exact superpose eq15 eq95507
    | exact resolve eq95507 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95507
  have eq165569 : (σ x) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq95508
       have i₂ := eq46949 x
       grind)
    | exact superpose eq46949 eq95508
    | (have j1 := eq46949 x
       grind)
    | exact resolve eq95508 eq46949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46949 eq95508
  have eq165579 : (σ x) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq165569
  have eq165591 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1729 x
       have i₂ := eq165579
       grind)
    | exact superpose eq165579 eq1729
    | (have j0 := eq1729 x
       grind)
    | exact resolve eq1729 eq165579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729 eq165579
  have eq165600 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq165591
  have eq165625 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq165600
       grind)
    | exact superpose eq165600 eq10
    | exact resolve eq10 eq165600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165600
  have eq165720 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq165625
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq165625
    | exact resolve eq165625 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165625
  have eq165721 : x = (M.op x x) := by grind
  clear eq165720
  have eq165789 : ∀ X0 : G, x ≠ (k x x) ∨ x = (k (M.op X0 x) x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq93542 x X0
       have i₂ := eq165721
       grind)
    | exact superpose eq165721 eq93542
    | (have j0 := eq93542 x X0
       grind)
    | exact resolve eq93542 eq165721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93542
  have eq165851 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq29 x X0 x
       have i₂ := eq165721
       grind)
    | exact superpose eq165721 eq29
    | exact resolve eq29 eq165721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq165721
  have eq166298 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq165851 X0
       have i₂ := eq25 X0 x
       grind)
    | exact superpose eq25 eq165851
    | exact resolve eq165851 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq165851
  have eq166302 : ∀ X0 : G, x ≠ x ∨ x = (k (M.op X0 x) x) ∨ x = (M.op X0 x) := by
    intro X0
    grind
  clear eq165789
  have eq166303 : ∀ X0 : G, x = (k (M.op X0 x) x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq166302 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166302
  have eq166310 : ∀ X0 : G, x = (k X0 x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq166303 X0
       have i₂ := eq166298 X0
       grind)
    | exact superpose eq166298 eq166303
    | (have j0 := eq166303 X0
       grind)
    | exact resolve eq166303 eq166298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166303
  have eq166315 : ∀ X0 : G, x = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq166310 X0
       have i₂ := eq166298 X0
       grind)
    | exact superpose eq166298 eq166310
    | (have j0 := eq166310 X0
       grind)
    | exact resolve eq166310 eq166298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166310
  have eq168915 : x = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71 x
       have i₂ := eq166315 (τ (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq166315 eq71
    | (have j0 := eq71 x
       have j1 := eq166315 (τ (M.op (σ x) (σ x)))
       grind)
    | exact resolve eq71 eq166315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq166315
  have eq169038 : x = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq168915
  have eq231697 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ x))
       have i₂ := eq169038
       grind)
    | exact superpose eq169038 eq11
    | exact resolve eq11 eq169038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169038
  have eq231732 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq231697
  have eq231807 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq66842
       have i₂ := eq231732
       grind)
    | exact superpose eq231732 eq66842
    | exact resolve eq66842 eq231732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66842 eq231732
  have eq232194 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq231807
       have i₂ := eq166298 x
       grind)
    | exact superpose eq166298 eq231807
    | exact resolve eq231807 eq166298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166298 eq231807
  have eq232195 : False := by grind
  exact eq232195

/-- `Equation4343`: `x ◇ (y ◇ y) = y ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pyx_Equation4343 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4343 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4343.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X0)) := by
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
  clear eq17
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
  have eq59 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
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
  have eq69 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq59 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq112 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq69 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq112 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq113 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq113 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq113 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq121 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq117 (σ X0)
       grind)
    | exact superpose eq117 eq15
    | exact resolve eq15 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq117 (τ X0)
       grind)
    | exact superpose eq117 eq31
    | exact resolve eq31 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq130 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq123 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq123
    | exact resolve eq123 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq132 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq121 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq121
    | exact resolve eq121 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq191 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 X1)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq9
    | exact resolve eq9 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq348 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X1 X1))) = (M.op (σ X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 (σ X1)
       have i₂ := eq132 X1
       grind)
    | exact superpose eq132 eq191
    | exact resolve eq191 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq69268 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq194 X0 X1
       grind)
    | exact superpose eq194 eq10
    | (have j1 := eq194 X0 X1
       grind)
    | exact resolve eq10 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq69686 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq69268 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq69268
    | (have j0 := eq69268 X0 X1
       grind)
    | exact resolve eq69268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69268
  have eq71899 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq69686 X1 (σ X0)
       grind)
    | exact superpose eq69686 eq15
    | (have j1 := eq69686 X1 X1
       grind)
    | exact resolve eq15 eq69686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69686
  have eq72058 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71899 X0 X1
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq71899
    | (have j0 := eq71899 X0 X1
       grind)
    | exact resolve eq71899 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71899
  have eq91567 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq266 X0 X1
       grind)
    | exact superpose eq266 eq11
    | (have j1 := eq266 X0 X1
       grind)
    | exact resolve eq11 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq91613 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq91567 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91567
    | (have j0 := eq91567 X0 X1
       grind)
    | exact resolve eq91567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91567
  have eq93177 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq91613 X0 X1
       grind)
    | exact superpose eq91613 eq18
    | (have j1 := eq91613 X0 X0
       grind)
    | exact resolve eq18 eq91613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq91613
  have eq95593 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (σ (M.op (τ (σ X0)) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq132 X0
       have i₂ := eq93177 (σ X0) X1
       grind)
    | exact superpose eq93177 eq132
    | (have j1 := eq93177 (σ X0) X1
       grind)
    | exact resolve eq132 eq93177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq93177
  have eq95640 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq95593 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95593
    | (have j0 := eq95593 X0 X1
       grind)
    | exact resolve eq95593 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95593
  have eq95655 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq95640 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq95640
    | (have j0 := eq95640 X0 X1
       grind)
    | exact resolve eq95640 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95640
  have eq134640 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72058 x y
       grind)
    | exact superpose eq72058 eq16
    | (have j1 := eq72058 x y
       grind)
    | exact resolve eq16 eq72058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72058
  have eq134688 : (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq95655 x y
       grind)
    | (have r₁ := eq134640
       have r₂ := eq95655 x y
       grind)
    | exact resolve eq134640 eq95655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95655 eq134640
  have eq134748 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq192 x X0
       have i₂ := eq134688
       grind)
    | exact superpose eq134688 eq192
    | (have j0 := eq192 x X0
       grind)
    | (have r₁ := eq192 x x
       have r₂ := eq134688
       grind)
    | exact resolve eq192 eq134688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134777 : (M.op x x) = (τ (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq134688
       grind)
    | exact superpose eq134688 eq10
    | exact resolve eq10 eq134688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134688
  have eq134819 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq134748 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134748
  have eq134839 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq134777
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq134777
    | exact resolve eq134777 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134777
  have eq135150 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k x X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq134819 (σ X0)
       grind)
    | exact superpose eq134819 eq15
    | exact resolve eq15 eq134819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134819
  have eq135811 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq135150 y
       grind)
    | exact superpose eq135150 eq16
    | exact resolve eq16 eq135150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135843 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ (k x x))) ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq263 (σ x) X0
       have i₂ := eq135150 x
       grind)
    | exact superpose eq135150 eq263
    | (have j0 := eq263 (σ x) X0
       grind)
    | exact resolve eq263 eq135150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq135150
  have eq135988 : ∀ X0 : G, (τ (σ x)) ≠ (k x x) ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq135843 X0
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq135843
    | (have j0 := eq135843 X0
       grind)
    | exact resolve eq135843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135843
  have eq136053 : ∀ X0 : G, (M.op x x) ≠ (τ (σ x)) ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq135988 X0
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq135988
    | (have j0 := eq135988 X0
       grind)
    | exact resolve eq135988 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq135988
  have eq136086 : ∀ X0 : G, x ≠ (M.op x x) ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq136053 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq136053
    | (have j0 := eq136053 X0
       grind)
    | exact resolve eq136053 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136053
  have eq136091 : ∀ X0 : G, (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq136086 X0
       grind)
    | (have r₁ := eq136086 X0
       have r₂ := eq134839
       grind)
    | exact resolve eq136086 eq134839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134839 eq136086
  have eq136093 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq136091 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq136091
    | exact resolve eq136091 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136091
  have eq136263 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq135811
       have i₂ := eq136093 y
       grind)
    | exact superpose eq136093 eq135811
    | exact resolve eq135811 eq136093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135811 eq136093
  have eq136288 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by grind
  clear eq136263
  have eq136289 : y = (M.op y y) := by grind
  clear eq136288
  have eq136322 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq9 y X0
       have i₂ := eq136289
       grind)
    | exact superpose eq136289 eq9
    | exact resolve eq9 eq136289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136323 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq136289
       grind)
    | exact superpose eq136289 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq136289
       grind)
    | exact resolve eq12 eq136289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136339 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq192 y X0
       have i₂ := eq136289
       grind)
    | exact superpose eq136289 eq192
    | (have j0 := eq192 y X0
       grind)
    | exact resolve eq192 eq136289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq136475 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq136339 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136339
  have eq136477 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq136323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136323
  have eq137328 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq136475 (σ X0)
       grind)
    | exact superpose eq136475 eq15
    | exact resolve eq15 eq136475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136475
  have eq137498 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq137328 X0
       have i₂ := eq136477 X0
       grind)
    | exact superpose eq136477 eq137328
    | exact resolve eq137328 eq136477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136477 eq137328
  have eq139647 : ∀ X0 : G, (M.op (σ X0) (σ (M.op y y))) = (σ (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq348 y X0
       have i₂ := eq137498 (M.op X0 X0)
       grind)
    | exact superpose eq137498 eq348
    | exact resolve eq348 eq137498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq137498
  have eq139888 : ∀ X0 : G, (M.op (σ X0) (σ (M.op y y))) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq139647 X0
       have i₂ := eq136322 X0
       grind)
    | exact superpose eq136322 eq139647
    | exact resolve eq139647 eq136322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136322 eq139647
  have eq139987 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq139888 X0
       have i₂ := eq136289
       grind)
    | exact superpose eq136289 eq139888
    | exact resolve eq139888 eq136289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136289 eq139888
  have eq141618 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq139987 x
       grind)
    | exact superpose eq139987 eq16
    | (have r₁ := eq16
       have r₂ := eq139987 x
       grind)
    | exact resolve eq16 eq139987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139987
  have eq141774 : False := by grind
  exact eq141774

/-- `Equation4343`: `x ◇ (y ◇ y) = y ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation4343 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4343 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4343.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
  clear eq17
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq84 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq16
    | (have j1 := eq36 x y
       grind)
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq486 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) (τ X1)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq92
    | (have j0 := eq92 (τ X0) (τ X1)
       grind)
    | exact resolve eq92 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq486 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq486
    | (have j0 := eq486 X0 X1
       grind)
    | exact resolve eq486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq496 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq493
    | (have j0 := eq493 X0 X1
       grind)
    | exact resolve eq493 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq498 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq496 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq496
    | (have j0 := eq496 X0 X1
       grind)
    | exact resolve eq496 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq499 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq498 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq498
    | (have j0 := eq498 X0 X1
       grind)
    | exact resolve eq498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq500 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq499 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq499
    | (have j0 := eq499 X0 X1
       grind)
    | exact resolve eq499 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq501 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq500 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq500
    | (have j0 := eq500 X0 X1
       grind)
    | exact resolve eq500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq516 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (τ X0) (τ X1)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq93
    | (have j0 := eq93 (τ X0) (τ X1)
       grind)
    | exact resolve eq93 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq524 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq516 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq516
    | (have j0 := eq516 X0 X1
       grind)
    | exact resolve eq516 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq527 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq524 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq524
    | (have j0 := eq524 X0 X1
       grind)
    | exact resolve eq524 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq529 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq527 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq527
    | (have j0 := eq527 X0 X1
       grind)
    | exact resolve eq527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq530 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq529 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq529
    | (have j0 := eq529 X0 X1
       grind)
    | exact resolve eq529 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq531 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq530 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq530
    | (have j0 := eq530 X0 X1
       grind)
    | exact resolve eq530 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq532 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq531 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq531
    | (have j0 := eq531 X0 X1
       grind)
    | exact resolve eq531 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq84
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq544 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq543
  have eq4289 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq544
       grind)
    | exact superpose eq544 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq544
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq544
       grind)
    | exact resolve eq13 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4291 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq544
  have eq4292 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4289
  have eq4293 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4292
       have r₂ := eq4291
       grind)
    | exact resolve eq4292 eq4291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4291 eq4292
  have eq4295 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4293
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4293
    | exact resolve eq4293 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4293
  have eq30115 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq4295
       grind)
    | exact superpose eq4295 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq4295
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq4295
       grind)
    | exact resolve eq12 eq4295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4295
  have eq30116 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq30115
  have eq30119 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30116
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq30116
    | exact resolve eq30116 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30116
  have eq30731 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq30119
       grind)
    | exact superpose eq30119 eq10
    | exact resolve eq10 eq30119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30119
  have eq30904 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30731
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq30731
    | exact resolve eq30731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30731
  have eq30907 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq501 x y
       grind)
    | (have r₁ := eq30904
       have r₂ := eq501 x y
       grind)
    | exact resolve eq30904 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq30904
  have eq31244 : (k x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq30907
       grind)
    | exact superpose eq30907 eq10
    | exact resolve eq10 eq30907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30907
  have eq31419 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31244
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq31244
    | exact resolve eq31244 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31244
  have eq31420 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq532 x y
       grind)
    | (have r₁ := eq31419
       have r₂ := eq532 x y
       grind)
    | exact resolve eq31419 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq31419
  have eq31759 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq31420
       grind)
    | exact superpose eq31420 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq31420
       grind)
    | exact resolve eq13 eq31420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31761 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq31762 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq31759
  have eq31763 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq31762
       have r₂ := eq31761
       grind)
    | exact resolve eq31762 eq31761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31762
  have eq32432 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93 x y
       have i₂ := eq31763
       grind)
    | exact superpose eq31763 eq93
    | (have j0 := eq93 x y
       grind)
    | exact resolve eq93 eq31763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq32476 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32432
  have eq107165 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32476
       grind)
    | exact superpose eq32476 eq16
    | exact resolve eq16 eq32476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32476
  have eq107272 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107165
       have i₂ := eq31420
       grind)
    | exact superpose eq31420 eq107165
    | exact resolve eq107165 eq31420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107165
  have eq107275 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq107272
  have eq107276 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq107275
       have r₂ := eq31761
       grind)
    | exact resolve eq107275 eq31761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107275
  have eq107332 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq107276
       grind)
    | exact superpose eq107276 eq16
    | exact resolve eq16 eq107276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107333 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq107276
       grind)
    | exact superpose eq107276 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq107276
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq107276
       grind)
    | exact resolve eq12 eq107276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107276
  have eq107334 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq107333
  have eq107337 : (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107334
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq107334
    | exact resolve eq107334 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107334
  have eq107399 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107332
       have i₂ := eq31420
       grind)
    | exact superpose eq31420 eq107332
    | exact resolve eq107332 eq31420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31420 eq107332
  have eq107403 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq107399
       have r₂ := eq31761
       grind)
    | exact resolve eq107399 eq31761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31761 eq107399
  have eq107528 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107337
       have i₂ := eq31763
       grind)
    | exact superpose eq31763 eq107337
    | exact resolve eq107337 eq31763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31763
  have eq107566 : (k x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq107337
       grind)
    | exact superpose eq107337 eq10
    | exact resolve eq10 eq107337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107337
  have eq107664 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq107528
  have eq107721 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107566
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq107566
    | exact resolve eq107566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107566
  have eq107748 : x = (M.op x y) := by
    first
    | (have r₁ := eq107664
       have r₂ := eq107403
       grind)
    | exact resolve eq107664 eq107403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107403 eq107664
  have eq107749 : y = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq107721
       have r₂ := eq12 x y
       grind)
    | exact resolve eq107721 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107721
  have eq107875 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq92 x y
       have i₂ := eq107749
       grind)
    | exact superpose eq107749 eq92
    | (have j0 := eq92 x y
       grind)
    | exact resolve eq92 eq107749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq107914 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq107875
  have eq109552 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq107914
       grind)
    | exact superpose eq107914 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq107914
       grind)
    | exact resolve eq13 eq107914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109554 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq107914
  have eq109555 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq109552
  have eq109556 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq109555
       have r₂ := eq109554
       grind)
    | exact resolve eq109555 eq109554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109555
  have eq109559 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109556
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq109556
    | exact resolve eq109556 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109556
  have eq109561 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109559
       have i₂ := eq107749
       grind)
    | exact superpose eq107749 eq109559
    | exact resolve eq109559 eq107749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107749 eq109559
  have eq109562 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq109561
       have r₂ := eq109554
       grind)
    | exact resolve eq109561 eq109554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109554 eq109561
  have eq109597 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq109562
       grind)
    | exact superpose eq109562 eq16
    | exact resolve eq16 eq109562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109562
  have eq109601 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq109597
       have i₂ := eq107748
       grind)
    | exact superpose eq107748 eq109597
    | exact resolve eq109597 eq107748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107748 eq109597
  have eq109602 : False := by grind
  exact eq109602

/-- `Equation436`: `x = x ◇ (y ◇ (y ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation436 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law436 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law436.models_iff G M).mp hM
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
  clear eq17
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq84 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq16
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq428 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq90
    | (have j0 := eq90 (τ X0) (τ X1)
       grind)
    | exact resolve eq90 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq428 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq428
    | (have j0 := eq428 X0 X1
       grind)
    | exact resolve eq428 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq438 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq435 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq435
    | (have j0 := eq435 X0 X1
       grind)
    | exact resolve eq435 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq440 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq438 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq438
    | (have j0 := eq438 X0 X1
       grind)
    | exact resolve eq438 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq441 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq440 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq440
    | (have j0 := eq440 X0 X1
       grind)
    | exact resolve eq440 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq442 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq441
    | (have j0 := eq441 X0 X1
       grind)
    | exact resolve eq441 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq443 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq442 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq442
    | (have j0 := eq442 X0 X1
       grind)
    | exact resolve eq442 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq458 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq91
    | (have j0 := eq91 (τ X0) (τ X1)
       grind)
    | exact resolve eq91 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq466 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq458 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq458
    | (have j0 := eq458 X0 X1
       grind)
    | exact resolve eq458 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq469 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq466
    | (have j0 := eq466 X0 X1
       grind)
    | exact resolve eq466 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq471 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq469
    | (have j0 := eq469 X0 X1
       grind)
    | exact resolve eq469 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq472 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq471 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq471
    | (have j0 := eq471 X0 X1
       grind)
    | exact resolve eq471 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq473 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq472 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq472
    | (have j0 := eq472 X0 X1
       grind)
    | exact resolve eq472 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq474 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq473 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq473
    | (have j0 := eq473 X0 X1
       grind)
    | exact resolve eq473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq485 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq84
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq485
  have eq3325 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq486
       grind)
    | exact superpose eq486 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq486
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq486
       grind)
    | exact resolve eq12 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq3327 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3325
  have eq3328 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3327
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3327
    | exact resolve eq3327 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327
  have eq20674 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3328
       grind)
    | exact superpose eq3328 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3328
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3328
       grind)
    | exact resolve eq13 eq3328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20675 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq3328
       grind)
    | exact superpose eq3328 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3328
       grind)
    | exact resolve eq12 eq3328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328
  have eq20676 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20674
  have eq20679 : (σ x) = (σ (k x y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20675
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq20675
    | exact resolve eq20675 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20675
  have eq20680 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20679
  have eq20681 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20676
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq20676
    | exact resolve eq20676 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20676
  have eq20683 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20681
       have r₂ := eq20680
       grind)
    | exact resolve eq20681 eq20680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20680 eq20681
  have eq21451 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq20683
       grind)
    | exact superpose eq20683 eq10
    | exact resolve eq10 eq20683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20683
  have eq21605 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21451
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq21451
    | exact resolve eq21451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21451
  have eq21608 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq474 x y
       grind)
    | (have r₁ := eq21605
       have r₂ := eq474 x y
       grind)
    | exact resolve eq21605 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq21605
  have eq21633 : (k x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq21608
       grind)
    | exact superpose eq21608 eq10
    | exact resolve eq10 eq21608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21608
  have eq21787 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21633
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21633
    | exact resolve eq21633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21633
  have eq21788 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq443 x y
       grind)
    | (have r₁ := eq21787
       have r₂ := eq443 x y
       grind)
    | exact resolve eq21787 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq21787
  have eq22235 : y ≠ y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq21788
       grind)
    | exact superpose eq21788 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq21788
       grind)
    | exact resolve eq12 eq21788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22236 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq22237 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq22235
  have eq22958 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90 x y
       have i₂ := eq22237
       grind)
    | exact superpose eq22237 eq90
    | (have j0 := eq90 x y
       grind)
    | exact resolve eq90 eq22237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq23003 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22958
  have eq28856 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23003
       grind)
    | exact superpose eq23003 eq16
    | exact resolve eq16 eq23003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23003
  have eq29554 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28856
       have i₂ := eq21788
       grind)
    | exact superpose eq21788 eq28856
    | exact resolve eq28856 eq21788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28856
  have eq29557 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq29554
  have eq29558 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq29557
       have r₂ := eq22236
       grind)
    | exact resolve eq29557 eq22236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29557
  have eq29908 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29558
       grind)
    | exact superpose eq29558 eq16
    | exact resolve eq16 eq29558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29909 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq29558
       grind)
    | exact superpose eq29558 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq29558
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq29558
       grind)
    | exact resolve eq13 eq29558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29558
  have eq29911 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq29909
  have eq29915 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29911
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq29911
    | exact resolve eq29911 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29911
  have eq30277 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29908
       have i₂ := eq21788
       grind)
    | exact superpose eq21788 eq29908
    | exact resolve eq29908 eq21788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21788 eq29908
  have eq30281 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30277
       have r₂ := eq22236
       grind)
    | exact resolve eq30277 eq22236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22236 eq30277
  have eq31303 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29915
       have i₂ := eq22237
       grind)
    | exact superpose eq22237 eq29915
    | exact resolve eq29915 eq22237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22237 eq29915
  have eq31443 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq31303
  have eq31562 : x = (M.op x y) := by
    first
    | (have r₁ := eq31443
       have r₂ := eq30281
       grind)
    | exact resolve eq31443 eq30281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30281 eq31443
  have eq31962 : x ≠ x ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq31562
       grind)
    | exact superpose eq31562 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq31562
       grind)
    | exact resolve eq13 eq31562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31963 : x ≠ y ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq31562
       grind)
    | exact superpose eq31562 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq31562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31964 : y = (k x y) ∨ x = y := by grind
  clear eq31962
  have eq32683 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq91 x y
       have i₂ := eq31964
       grind)
    | exact superpose eq31964 eq91
    | (have j0 := eq91 x y
       grind)
    | exact resolve eq91 eq31964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq32709 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq32683
  have eq34993 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq32709
       grind)
    | exact superpose eq32709 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq32709
       grind)
    | exact resolve eq12 eq32709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32709
  have eq34995 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq34993
  have eq34996 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq34995
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq34995
    | exact resolve eq34995 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34995
  have eq36664 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq34996
       grind)
    | exact superpose eq34996 eq16
    | exact resolve eq16 eq34996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34996
  have eq36673 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq36664
       have i₂ := eq31562
       grind)
    | exact superpose eq31562 eq36664
    | exact resolve eq36664 eq31562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36664
  have eq36674 : (σ x) = (σ (k x y)) ∨ x = y := by grind
  clear eq36673
  have eq37236 : (k x y) = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq36674
       grind)
    | exact superpose eq36674 eq10
    | exact resolve eq10 eq36674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36674
  have eq37432 : x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq37236
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq37236
    | exact resolve eq37236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37236
  have eq37433 : x = (k x y) := by
    first
    | (have r₁ := eq37432
       have r₂ := eq31963
       grind)
    | exact resolve eq37432 eq31963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31963 eq37432
  have eq37849 : x = y ∨ x = y := by
    first
    | (have i₁ := eq31964
       have i₂ := eq37433
       grind)
    | exact superpose eq37433 eq31964
    | exact resolve eq31964 eq37433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31964
  have eq37880 : x = y := by grind
  clear eq37849
  have eq38240 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37880
       grind)
    | exact superpose eq37880 eq16
    | exact resolve eq16 eq37880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38241 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq37880
       grind)
    | exact superpose eq37880 eq84
    | exact resolve eq84 eq37880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq38273 : x = (M.op x x) := by
    first
    | (have i₁ := eq31562
       have i₂ := eq37880
       grind)
    | exact superpose eq37880 eq31562
    | exact resolve eq31562 eq37880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31562
  have eq38275 : x = (k x x) := by
    first
    | (have i₁ := eq37433
       have i₂ := eq37880
       grind)
    | exact superpose eq37880 eq37433
    | exact resolve eq37433 eq37880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37433 eq37880
  have eq38304 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq38241
  have eq38305 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq38304
       have i₂ := eq38275
       grind)
    | exact superpose eq38275 eq38304
    | exact resolve eq38304 eq38275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38275 eq38304
  have eq38306 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq38240
       have i₂ := eq38273
       grind)
    | exact superpose eq38273 eq38240
    | exact resolve eq38240 eq38273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38240
  have eq38307 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq38305
       have i₂ := eq38273
       grind)
    | exact superpose eq38273 eq38305
    | exact resolve eq38305 eq38273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38273 eq38305
  have eq38308 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq38307
  have eq38309 : False := by grind
  exact eq38309
