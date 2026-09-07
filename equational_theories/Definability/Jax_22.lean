import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4389`: `x ◇ (x ◇ x) = (y ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_y_pxx_x_pyx_Equation4389 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4389 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4389.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
  have eq24 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X2 X2) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq9 x X2
       have i₂ := eq9 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq9 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X1 X1)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op X1 X1)
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
  have eq39 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq19
    | exact resolve eq19 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
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
  clear eq37
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq40
    | exact resolve eq40 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq40
  have eq46 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    grind
  have eq47 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq46
    | (have j0 := eq46 X0
       grind)
    | exact resolve eq46 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq48 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq47
    | (have j0 := eq47 X0
       grind)
    | exact resolve eq47 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
       have r₂ := eq14 X0 (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq121 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq24
    | exact resolve eq24 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq25
    | exact resolve eq25 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq10
    | exact resolve eq10 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X1 X1) X1) ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 (M.op X0 X0) X0
       have i₂ := eq25 X0 X1
       grind)
    | (have i₁ := eq73 (M.op X1 X1) X1
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq73
    | (have j0 := eq73 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq73 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op X1 (M.op X1 X1))
       have r₂ := eq25 (M.op X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq73 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))
       have r₂ := eq25 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq73 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq189 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq34
    | (have j0 := eq34 X0 X1
       grind)
    | exact resolve eq34 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq207 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq24
    | exact resolve eq24 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq25
    | exact resolve eq25 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq262 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq259 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq259 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq259 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq259 X0 X1
       have r₂ := eq14 X0 (M.op X1 X0)
       grind)
    | exact resolve eq259 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq317 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1
       have i₂ := eq262 (σ X1) X0
       grind)
    | (have i₁ := eq42 X0
       have i₂ := eq262 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq262 eq42
    | (have j1 := eq262 (σ X1) X0
       grind)
    | exact resolve eq42 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 X1 : G, (M.op X1 X1) = (σ X0) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1
       have i₂ := eq262 (τ X1) X0
       grind)
    | (have i₁ := eq44 X0
       have i₂ := eq262 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq262 eq44
    | (have j1 := eq262 (τ X1) X0
       grind)
    | exact resolve eq44 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (M.op (σ X1) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X1 (τ X0)
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq121
    | exact resolve eq121 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X2 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ X2) (σ (M.op X2 X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq121 X2 x
       have i₂ := eq121 X0 x
       grind)
    | exact superpose eq121 eq121
    | exact resolve eq121 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1791 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq24
    | (have j1 := eq48 X0
       grind)
    | exact resolve eq24 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq48
  have eq1811 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (τ (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1791 X0 X1
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq1791
    | (have j0 := eq1791 X0 X1
       grind)
    | exact resolve eq1791 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1791
  have eq2243 : ∀ X0 X1 : G, (M.op X1 X1) = (τ X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq317 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq317 (σ X0) X1
       grind)
    | exact superpose eq317 eq10
    | (have j1 := eq317 X0 X1
       grind)
    | exact resolve eq10 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq2499 : ∀ X0 X1 : G, (k (σ (τ X1)) X0) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X1 X1) = (σ (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (τ X1)
       have i₂ := eq319 (τ X0) X1
       grind)
    | exact superpose eq319 eq19
    | (have j1 := eq319 (τ X0) X1
       grind)
    | exact resolve eq19 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq319
  have eq2503 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X1 X1) = (σ (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2499 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2499
    | (have j0 := eq2499 X0 X1
       grind)
    | exact resolve eq2499 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2499
  have eq2531 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2503 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2503
    | (have j0 := eq2503 X0 X1
       grind)
    | exact resolve eq2503 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503
  have eq6346 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq162 X0 (M.op X0 (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq6740 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (τ (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2243 (σ X0) X1
       grind)
    | exact superpose eq2243 eq15
    | (have j1 := eq2243 (σ X0) X1
       grind)
    | exact resolve eq15 eq2243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2243
  have eq6775 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6740 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6740
    | (have j0 := eq6740 X0 X1
       grind)
    | exact resolve eq6740 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6740
  have eq14609 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6775 x y
       grind)
    | exact superpose eq6775 eq16
    | (have j1 := eq6775 x y
       grind)
    | exact resolve eq16 eq6775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6775
  have eq15595 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14609
       have i₂ := eq262 y x
       grind)
    | exact superpose eq262 eq14609
    | (have j1 := eq262 y x
       grind)
    | exact resolve eq14609 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq14609
  have eq15598 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq15595
  have eq15599 : x = (M.op y y) := by grind
  clear eq15598
  have eq16147 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq15599
       grind)
    | exact superpose eq15599 eq9
    | exact resolve eq9 eq15599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16153 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq25 X0 y
       have i₂ := eq15599
       grind)
    | exact superpose eq15599 eq25
    | exact resolve eq25 eq15599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq16158 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq121 y X0
       have i₂ := eq15599
       grind)
    | exact superpose eq15599 eq121
    | exact resolve eq121 eq15599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq16159 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq122 y X0
       have i₂ := eq15599
       grind)
    | exact superpose eq15599 eq122
    | exact resolve eq122 eq15599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq16160 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq127 y X0
       have i₂ := eq15599
       grind)
    | exact superpose eq15599 eq127
    | exact resolve eq127 eq15599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq16168 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (τ x) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq207 y X0
       have i₂ := eq15599
       grind)
    | exact superpose eq15599 eq207
    | exact resolve eq207 eq15599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq16179 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (τ x) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq369 y X0
       have i₂ := eq15599
       grind)
    | exact superpose eq15599 eq369
    | exact resolve eq369 eq15599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq16181 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq370 X0 y
       have i₂ := eq15599
       grind)
    | exact superpose eq15599 eq370
    | exact resolve eq370 eq15599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq16226 : (M.op (σ y) (σ x)) = (M.op (τ x) (τ y)) := by
    first
    | (have i₁ := eq16179 x
       have i₂ := eq16181 x
       grind)
    | exact superpose eq16181 eq16179
    | exact resolve eq16179 eq16181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16179 eq16181
  have eq16228 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16158 x
       have i₂ := eq16160 x
       grind)
    | exact superpose eq16160 eq16158
    | exact resolve eq16158 eq16160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16158 eq16160
  have eq16670 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16147 y
       have i₂ := eq15599
       grind)
    | exact superpose eq15599 eq16147
    | exact resolve eq16147 eq15599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15599
  have eq16705 : ∀ X1 : G, (M.op x y) = (M.op (σ X1) (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq139 X1 x
       have i₂ := eq16147 x
       grind)
    | exact superpose eq16147 eq139
    | exact resolve eq139 eq16147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16709 : ∀ X1 : G, (M.op x y) = (M.op (τ X1) (τ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq209 X1 x
       have i₂ := eq16147 x
       grind)
    | exact superpose eq16147 eq209
    | exact resolve eq209 eq16147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq23673 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16147 x
       have i₂ := eq16159 x
       grind)
    | exact superpose eq16159 eq16147
    | exact resolve eq16147 eq16159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16147
  have eq23697 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq16159 X0
       grind)
    | exact superpose eq16159 eq16
    | exact resolve eq16 eq16159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16159
  have eq23734 : (σ (M.op x y)) ≠ (M.op y x) := by
    first
    | (have i₁ := eq23697 x
       have i₂ := eq16153 x
       grind)
    | exact superpose eq16153 eq23697
    | exact resolve eq23697 eq16153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23697
  have eq23784 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq23734
       have i₂ := eq16670
       grind)
    | exact superpose eq16670 eq23734
    | exact resolve eq23734 eq16670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23734
  have eq34275 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (M.op X0 X0) X0)) ∨ (k X1 (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1)
       have i₂ := eq1811 X1 X0
       grind)
    | exact superpose eq1811 eq11
    | (have j1 := eq1811 X1 X1
       grind)
    | exact resolve eq11 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34351 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (M.op (M.op X1 X1) X1) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq1811 (τ X0) X1
       grind)
    | exact superpose eq1811 eq18
    | (have j1 := eq1811 (τ X0) X1
       grind)
    | exact resolve eq18 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq34359 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (M.op (M.op X1 X1) X1) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34351 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq34351
    | (have j0 := eq34351 X0 X1
       grind)
    | exact resolve eq34351 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34351
  have eq34419 : ∀ X1 : G, (M.op X1 X1) = (σ (M.op (τ x) (τ y))) ∨ (k X1 (M.op X1 X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq34275 x X1
       have i₂ := eq16168 x
       grind)
    | exact superpose eq16168 eq34275
    | (have j0 := eq34275 x X1
       grind)
    | exact resolve eq34275 eq16168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34275
  have eq34519 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X1 X1) X1) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34359 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34359
    | (have j0 := eq34359 X0 X1
       grind)
    | exact resolve eq34359 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34359
  have eq34579 : ∀ X1 : G, (M.op X1 X1) = (σ (M.op (σ y) (σ x))) ∨ (k X1 (M.op X1 X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq34419 X1
       have i₂ := eq16226
       grind)
    | exact superpose eq16226 eq34419
    | (have j0 := eq34419 X1
       grind)
    | exact resolve eq34419 eq16226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34419
  have eq34669 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (τ (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34519 X0 X1
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq34519
    | (have j0 := eq34519 X0 X1
       grind)
    | exact resolve eq34519 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34519
  have eq34728 : ∀ X1 : G, (M.op X1 X1) = (σ (M.op (σ x) (σ y))) ∨ (k X1 (M.op X1 X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq34579 X1
       have i₂ := eq16228
       grind)
    | exact superpose eq16228 eq34579
    | (have j0 := eq34579 X1
       grind)
    | exact resolve eq34579 eq16228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34579
  have eq34818 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (M.op (τ x) (τ y)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq34669 X0 x
       have i₂ := eq16168 x
       grind)
    | exact superpose eq16168 eq34669
    | (have j0 := eq34669 X0 x
       grind)
    | exact resolve eq34669 eq16168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16168 eq34669
  have eq34877 : ∀ X1 : G, (k X1 (M.op X1 X1)) = X1 ∨ (M.op X1 X1) = (σ (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq34728 X1
       have i₂ := eq23673
       grind)
    | exact superpose eq23673 eq34728
    | (have j0 := eq34728 X1
       grind)
    | exact resolve eq34728 eq23673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34728
  have eq34965 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (M.op (σ y) (σ x)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq34818 X0
       have i₂ := eq16226
       grind)
    | exact superpose eq16226 eq34818
    | (have j0 := eq34818 X0
       grind)
    | exact resolve eq34818 eq16226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16226 eq34818
  have eq35061 : ∀ X0 : G, (M.op (σ x) (σ y)) = (τ (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq34965 X0
       have i₂ := eq16228
       grind)
    | exact superpose eq16228 eq34965
    | (have j0 := eq34965 X0
       grind)
    | exact resolve eq34965 eq16228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16228 eq34965
  have eq35148 : ∀ X0 : G, (M.op x y) = (τ (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq35061 X0
       have i₂ := eq23673
       grind)
    | exact superpose eq23673 eq35061
    | (have j0 := eq35061 X0
       grind)
    | exact resolve eq35061 eq23673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23673 eq35061
  have eq164630 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ (M.op x y)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq34877 (τ X0)
       grind)
    | exact superpose eq34877 eq18
    | (have j1 := eq34877 (τ X0)
       grind)
    | exact resolve eq18 eq34877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34877
  have eq164727 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (σ (M.op x y)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq164630 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq164630
    | (have j0 := eq164630 X0
       grind)
    | exact resolve eq164630 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164630
  have eq164803 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ (M.op x y)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq164727 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq164727
    | (have j0 := eq164727 X0
       grind)
    | exact resolve eq164727 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164727
  have eq164870 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ (M.op x y)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq164803 X0
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq164803
    | (have j0 := eq164803 X0
       grind)
    | exact resolve eq164803 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164803
  have eq265405 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ (M.op x y)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq164870 (τ X0)
       grind)
    | exact superpose eq164870 eq18
    | (have j1 := eq164870 (τ X0)
       grind)
    | exact resolve eq18 eq164870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq164870
  have eq265429 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (σ (M.op x y)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq265405 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq265405
    | (have j0 := eq265405 X0
       grind)
    | exact resolve eq265405 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq265405
  have eq265453 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ (M.op x y)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq265429 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq265429
    | (have j0 := eq265429 X0
       grind)
    | exact resolve eq265429 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265429
  have eq265473 : ∀ X0 : G, (σ (M.op x y)) = (τ (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq265453 X0
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq265453
    | (have j0 := eq265453 X0
       grind)
    | exact resolve eq265453 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq265453
  have eq528643 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq35148 X0
       have i₂ := eq265473 X0
       grind)
    | exact superpose eq265473 eq35148
    | (have j0 := eq35148 X0
       have j1 := eq265473 X0
       grind)
    | exact resolve eq35148 eq265473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35148 eq265473
  have eq528655 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq528643 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528643
  have eq528661 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq528655 X0
       grind)
    | (have r₁ := eq528655 X0
       have r₂ := eq23784
       grind)
    | exact resolve eq528655 eq23784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528655
  have eq532483 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq528661 X1
       have i₂ := eq2531 X0 X1
       grind)
    | (have i₁ := eq528661 X0
       have i₂ := eq2531 (M.op X0 X0) X1
       grind)
    | exact superpose eq2531 eq528661
    | (have j1 := eq2531 X0 X1
       grind)
    | exact resolve eq528661 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531 eq528661
  have eq548544 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq532483 X0 (M.op X0 X0)
       have i₂ := eq16709 X0
       grind)
    | exact superpose eq16709 eq532483
    | (have j0 := eq532483 X0 (M.op X0 X0)
       grind)
    | exact resolve eq532483 eq16709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16709 eq532483
  have eq574634 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op (σ X1) (σ (M.op X1 X1))) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       have i₂ := eq6346 X0
       grind)
    | exact superpose eq6346 eq189
    | (have j1 := eq6346 X0
       grind)
    | exact resolve eq189 eq6346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq6346
  have eq575131 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op (σ X1) (σ (M.op X1 X1))) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq574634 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574634
  have eq575139 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq575131 X0 x
       grind)
    | (have r₁ := eq575131 x X0
       have r₂ := eq139 X0 x
       grind)
    | exact resolve eq575131 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq575131
  have eq575143 : (M.op y x) = (k (M.op (M.op y x) (M.op y x)) (M.op y x)) := by
    first
    | (have i₁ := eq575139 x
       have i₂ := eq16153 x
       grind)
    | exact superpose eq16153 eq575139
    | exact resolve eq575139 eq16153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16153 eq575139
  have eq575147 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq575143
       have i₂ := eq16670
       grind)
    | exact superpose eq16670 eq575143
    | exact resolve eq575143 eq16670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16670 eq575143
  have eq2333794 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq548544 (M.op x y)
       have i₂ := eq575147
       grind)
    | exact superpose eq575147 eq548544
    | exact resolve eq548544 eq575147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548544 eq575147
  have eq2333799 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq2333794
       have r₂ := eq23784
       grind)
    | exact resolve eq2333794 eq23784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2333794
  have eq2333977 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq16705 (M.op x y)
       have i₂ := eq2333799
       grind)
    | exact superpose eq2333799 eq16705
    | exact resolve eq16705 eq2333799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16705
  have eq2334074 : (M.op x y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2333977
       have i₂ := eq42 (M.op x y)
       grind)
    | exact superpose eq42 eq2333977
    | exact resolve eq2333977 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2333977
  have eq2334226 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq2334074
       have i₂ := eq2333799
       grind)
    | exact superpose eq2333799 eq2334074
    | exact resolve eq2334074 eq2333799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2333799 eq2334074
  have eq2334326 : False := by grind
  exact eq2334326

/-- `Equation4396`: `x ◇ (x ◇ y) = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pxy_Equation4396 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4396 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4396.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X0) X1) := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq95 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq120 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq95 X0 (τ X1)
       grind)
    | exact superpose eq95 eq20
    | (have j1 := eq95 X0 (τ X1)
       grind)
    | exact resolve eq20 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq122 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq95 (σ X0) (σ X1)
       grind)
    | exact superpose eq95 eq15
    | (have j1 := eq95 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq95
  have eq154 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq129 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq155 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq154 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq190 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq155 (σ X0)
       grind)
    | exact superpose eq155 eq15
    | exact resolve eq15 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq190 X0
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq190
    | exact resolve eq190 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq190
  have eq296 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq197 X0
       grind)
    | exact superpose eq197 eq9
    | exact resolve eq9 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq307 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq299 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq299
    | exact resolve eq299 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq311 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq307
  have eq314 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq311 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq311
    | exact resolve eq311 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq1156 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq296 X0 (σ X0)
       have i₂ := eq197 X0
       grind)
    | exact superpose eq197 eq296
    | exact resolve eq296 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq1215 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1156 X0
       have i₂ := eq314 X0
       grind)
    | exact superpose eq314 eq1156
    | exact resolve eq1156 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq1156
  have eq4512 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120
    | exact resolve eq120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq4651 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4512 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4512
    | (have j0 := eq4512 X0 X1
       grind)
    | exact resolve eq4512 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4512
  have eq6548 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq122 X0 X1
       grind)
    | exact superpose eq122 eq10
    | (have j1 := eq122 X0 X1
       grind)
    | exact resolve eq10 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq6702 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6548 X0 X1
       have i₂ := eq197 X0
       grind)
    | exact superpose eq197 eq6548
    | (have j0 := eq6548 X0 X1
       grind)
    | exact resolve eq6548 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq6548
  have eq6833 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6702 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6702
    | (have j0 := eq6702 X0 X1
       grind)
    | exact resolve eq6702 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6702
  have eq8183 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6833 x y
       grind)
    | exact superpose eq6833 eq16
    | (have j1 := eq6833 x y
       grind)
    | exact resolve eq16 eq6833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6833
  have eq8281 : y = (M.op x x) := by
    first
    | (have j1 := eq4651 y x
       grind)
    | (have r₁ := eq8183
       have r₂ := eq4651 y x
       grind)
    | exact resolve eq8183 eq4651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4651 eq8183
  have eq8734 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1215 x
       have i₂ := eq8281
       grind)
    | exact superpose eq8281 eq1215
    | exact resolve eq1215 eq8281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215 eq8281
  have eq8747 : False := by grind
  exact eq8747

/-- `Equation4396`: `x ◇ (x ◇ y) = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pyx_Equation4396 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4396 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4396.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X0) X1) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq37 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  clear eq20
  have eq38 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq9 (τ X0) (τ X0)
       grind)
    | exact superpose eq9 eq37
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq40 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq522 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq80
  have eq7179 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq522 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq7181 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7179 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7179
  have eq7182 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7181 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7181
  have eq7309 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7182 (σ X0)
       grind)
    | exact superpose eq7182 eq15
    | exact resolve eq15 eq7182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7315 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0 X0
       have i₂ := eq7182 (τ X0)
       grind)
    | exact superpose eq7182 eq40
    | exact resolve eq40 eq7182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7322 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7315 X0
       have i₂ := eq7182 X0
       grind)
    | exact superpose eq7182 eq7315
    | exact resolve eq7315 eq7182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7315
  have eq7328 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7309 X0
       have i₂ := eq7182 X0
       grind)
    | exact superpose eq7182 eq7309
    | exact resolve eq7309 eq7182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7182 eq7309
  have eq7848 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ X0) X1)) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq7322 X0
       grind)
    | exact superpose eq7322 eq9
    | exact resolve eq9 eq7322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7851 : ∀ X0 : G, (k (τ (M.op X0 X0)) (τ X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    grind
  have eq7934 : ∀ X0 : G, (τ (k (M.op X0 X0) X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7851 X0
       have i₂ := eq40 X0 (M.op X0 X0)
       grind)
    | exact superpose eq40 eq7851
    | exact resolve eq7851 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq7851
  have eq7955 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    grind
  clear eq7934
  have eq7966 : ∀ X0 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7955 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq7955
    | exact resolve eq7955 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7955
  have eq8434 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq8518 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8434 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq8434
    | exact resolve eq8434 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8434
  have eq8545 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq8518
  have eq8559 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8545 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq8545
    | exact resolve eq8545 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8545
  have eq9429 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq7848 X0 (τ X0)
       grind)
    | exact superpose eq7848 eq38
    | exact resolve eq38 eq7848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq7848
  have eq9493 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9429 X0
       have i₂ := eq7966 X0
       grind)
    | exact superpose eq7966 eq9429
    | exact resolve eq9429 eq7966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7966 eq9429
  have eq9559 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq9493 X0
       have i₂ := eq11 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq11 eq9493
    | exact resolve eq9493 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9493
  have eq9599 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (σ (τ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq9559 X0
       have i₂ := eq7322 X0
       grind)
    | exact superpose eq7322 eq9559
    | exact resolve eq9559 eq7322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7322 eq9559
  have eq9633 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9599 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq9599
    | exact resolve eq9599 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9599
  have eq10646 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9633 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9633 X0
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq9633
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9633 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10656 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9633 X0
       have i₂ := eq85 X0 X1
       grind)
    | (have i₁ := eq9633 X0
       have i₂ := eq85 X0 (M.op X0 X0)
       grind)
    | exact superpose eq85 eq9633
    | (have j1 := eq85 X1 X0
       grind)
    | exact resolve eq9633 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq10715 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq10656 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10656
  have eq10719 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq10646 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10646
  have eq12426 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9633 X0
       have i₂ := eq10719 X0 X1
       grind)
    | (have i₁ := eq9633 X0
       have i₂ := eq10719 X0 (M.op X0 X0)
       grind)
    | exact superpose eq10719 eq9633
    | (have j1 := eq10719 X0 X1
       grind)
    | exact resolve eq9633 eq10719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9633
  have eq12453 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7328 X1
       have i₂ := eq10719 (σ X1) X0
       grind)
    | (have i₁ := eq7328 X0
       have i₂ := eq10719 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq10719 eq7328
    | (have j1 := eq10719 (σ X1) X0
       grind)
    | exact resolve eq7328 eq10719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7328
  have eq19976 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10715 X0 X1
       have i₂ := eq12426 X0 X1
       grind)
    | exact superpose eq12426 eq10715
    | (have j0 := eq10715 X0 X1
       have j1 := eq12426 X0 X1
       grind)
    | exact resolve eq10715 eq12426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10715 eq12426
  have eq20010 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq19976 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19976
  have eq24307 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq12453 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq12453 (σ X0) X1
       grind)
    | exact superpose eq12453 eq10
    | (have j1 := eq12453 X0 X1
       grind)
    | exact resolve eq10 eq12453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12453
  have eq26622 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq24307 (σ X0) X1
       grind)
    | exact superpose eq24307 eq15
    | (have j1 := eq24307 (σ X0) X1
       grind)
    | exact resolve eq15 eq24307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24307
  have eq26682 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26622 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26622
    | (have j0 := eq26622 X0 X1
       grind)
    | exact resolve eq26622 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26622
  have eq32457 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26682 x y
       grind)
    | exact superpose eq26682 eq16
    | (have j1 := eq26682 x y
       grind)
    | exact resolve eq16 eq26682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26682
  have eq33868 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq32457
       have i₂ := eq10719 y x
       grind)
    | exact superpose eq10719 eq32457
    | (have j1 := eq10719 y x
       grind)
    | exact resolve eq32457 eq10719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10719 eq32457
  have eq33879 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq33868
  have eq33880 : x = (M.op y y) := by grind
  clear eq33879
  have eq34693 : (M.op x y) = (k x y) := by grind
  have eq34720 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq8559 y
       have i₂ := eq33880
       grind)
    | exact superpose eq33880 eq8559
    | exact resolve eq8559 eq33880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8559 eq33880
  have eq35208 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq20010 x y
       have i₂ := eq34693
       grind)
    | exact superpose eq34693 eq20010
    | (have j0 := eq20010 x y
       grind)
    | exact resolve eq20010 eq34693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20010 eq34693
  have eq35209 : (M.op x y) = (M.op y x) := by grind
  clear eq35208
  have eq41476 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34720
       grind)
    | exact superpose eq34720 eq16
    | exact resolve eq16 eq34720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34720
  have eq41523 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq41476
       have i₂ := eq35209
       grind)
    | exact superpose eq35209 eq41476
    | exact resolve eq41476 eq35209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35209 eq41476
  have eq41524 : False := by grind
  exact eq41524

/-- `Equation4396`: `x ◇ (x ◇ y) = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pxy_Equation4396 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4396 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4396.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq88 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq521 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq79
  have eq1511 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq90 X1 X0
       grind)
    | exact superpose eq90 eq10
    | (have j1 := eq90 X1 X0
       grind)
    | exact resolve eq10 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq7025 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq521 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq7027 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7025 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7025
  have eq7028 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7027 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7027
  have eq7164 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7028 (σ X0)
       grind)
    | exact superpose eq7028 eq15
    | exact resolve eq15 eq7028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7183 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7164 X0
       have i₂ := eq7028 X0
       grind)
    | exact superpose eq7028 eq7164
    | exact resolve eq7164 eq7028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7028 eq7164
  have eq8205 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq7183 X0
       grind)
    | exact superpose eq7183 eq9
    | exact resolve eq9 eq7183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8208 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq8295 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8208 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq8208
    | exact resolve eq8208 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8208
  have eq8324 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq8295
  have eq8492 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq88
    | exact resolve eq88 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq8880 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8492 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq8492
    | (have j0 := eq8492 X0 X1
       grind)
    | exact resolve eq8492 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8492
  have eq12175 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8205 X0 (σ X0)
       have i₂ := eq7183 X0
       grind)
    | exact superpose eq7183 eq8205
    | exact resolve eq8205 eq7183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8205
  have eq12332 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12175 X0
       have i₂ := eq8324 X0
       grind)
    | exact superpose eq8324 eq12175
    | exact resolve eq12175 eq8324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12175
  have eq48178 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq1511 X1 X0
       grind)
    | exact superpose eq1511 eq10
    | (have j1 := eq1511 X1 X0
       grind)
    | exact resolve eq10 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq48669 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48178 X0 X1
       have i₂ := eq7183 X0
       grind)
    | exact superpose eq7183 eq48178
    | (have j0 := eq48178 X0 X1
       grind)
    | exact resolve eq48178 eq7183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48178
  have eq49343 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48669 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq48669
    | (have j0 := eq48669 X0 X1
       grind)
    | exact resolve eq48669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48669
  have eq49897 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq49343 X0 X1
       have i₂ := eq7183 X1
       grind)
    | exact superpose eq7183 eq49343
    | (have j0 := eq49343 X0 X1
       grind)
    | exact resolve eq49343 eq7183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7183 eq49343
  have eq50297 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq49897 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq49897
    | (have j0 := eq49897 X0 X1
       grind)
    | exact resolve eq49897 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49897
  have eq106067 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50297 x y
       grind)
    | exact superpose eq50297 eq16
    | (have j1 := eq50297 x y
       grind)
    | exact resolve eq16 eq50297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50297
  have eq106575 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq8880 x y
       grind)
    | (have r₁ := eq106067
       have r₂ := eq8880 y x
       grind)
    | exact resolve eq106067 eq8880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8880 eq106067
  have eq109183 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op x X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 y X0
       have i₂ := eq106575
       grind)
    | exact superpose eq106575 eq9
    | exact resolve eq9 eq106575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109235 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12332 y
       have i₂ := eq106575
       grind)
    | exact superpose eq106575 eq12332
    | exact resolve eq12332 eq106575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12332
  have eq116320 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq109183 y
       have i₂ := eq106575
       grind)
    | exact superpose eq106575 eq109183
    | exact resolve eq109183 eq106575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106575 eq109183
  have eq116470 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq116320
  have eq124886 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq109235
       grind)
    | exact superpose eq109235 eq16
    | exact resolve eq16 eq109235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109235
  have eq126300 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq124886
       have i₂ := eq116470
       grind)
    | exact superpose eq116470 eq124886
    | exact resolve eq124886 eq116470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116470 eq124886
  have eq126303 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq126300
  have eq126304 : y = (M.op x x) := by grind
  clear eq126303
  have eq127722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8324 x
       have i₂ := eq126304
       grind)
    | exact superpose eq126304 eq8324
    | exact resolve eq8324 eq126304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8324 eq126304
  have eq127810 : False := by grind
  exact eq127810

/-- `Equation4405`: `x ◇ (x ◇ y) = (y ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation4405 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4405 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4405.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq32 (τ X0)
       grind)
    | exact superpose eq32 eq18
    | exact resolve eq18 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq37
    | exact resolve eq37 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq37
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq79 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq84 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq86 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq90 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       have j1 := eq80 X1 X0
       grind)
    | (have r₁ := eq82 X0 X1
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq82 X1 X0
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq82 X1 X1
       have r₂ := eq80 X1 X1
       grind)
    | exact resolve eq82 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq82
  have eq93 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq135 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq10
    | exact resolve eq10 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq90
    | (have j0 := eq90 (σ X1) (σ X0)
       grind)
    | exact resolve eq90 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq90 X1 (τ X0)
       grind)
    | exact superpose eq90 eq17
    | (have j1 := eq90 X1 (τ X0)
       grind)
    | exact resolve eq17 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq90
  have eq339 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq312
    | (have j0 := eq312 X0 X1
       grind)
    | exact resolve eq312 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq348 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq292
    | (have j0 := eq292 X0 X1
       grind)
    | exact resolve eq292 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq357 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq339 X0 X1
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq339
    | (have j0 := eq339 X0 X1
       grind)
    | exact resolve eq339 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq339
  have eq362 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq348 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq348
    | (have j0 := eq348 X0 X1
       grind)
    | exact resolve eq348 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq1321 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq93 X0 X1
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1356 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1404 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1321 X0 X1
       have j1 := eq135 X0 (σ X1)
       grind)
    | (have r₁ := eq1321 X0 X0
       have r₂ := eq135 X0 (σ X0)
       grind)
    | (have r₁ := eq1321 X0 X1
       have r₂ := eq135 X0 (σ X1)
       grind)
    | exact resolve eq1321 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq1321
  have eq1469 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1404 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq1404
    | (have j0 := eq1404 X0 X1
       grind)
    | exact resolve eq1404 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1513 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1469 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq1469
    | (have j0 := eq1469 X0 X1
       grind)
    | exact resolve eq1469 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1537 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1513 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1513
    | (have j0 := eq1513 X0 X1
       grind)
    | exact resolve eq1513 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq7188 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq357 X0 X1
       grind)
    | exact superpose eq357 eq270
    | (have j0 := eq270 X0 X1
       have j1 := eq357 X0 X1
       grind)
    | (have r₁ := eq270 X0 X1
       have r₂ := eq357 X0 X1
       grind)
    | exact resolve eq270 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq7231 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq357 X0 X1
       grind)
    | exact superpose eq357 eq11
    | (have j1 := eq357 X0 X1
       grind)
    | exact resolve eq11 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq7397 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq7188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7188
  have eq12260 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1537 (τ X1) (τ X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq1537
    | (have j0 := eq1537 (τ X0) (τ X1)
       grind)
    | exact resolve eq1537 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12348 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12260 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq12260
    | (have j0 := eq12260 X0 X1
       grind)
    | exact resolve eq12260 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12260
  have eq12381 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12348 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq12348
    | (have j0 := eq12348 X0 X1
       grind)
    | exact resolve eq12348 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12348
  have eq12405 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12381 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq12381
    | (have j0 := eq12381 X0 X1
       grind)
    | exact resolve eq12381 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12381
  have eq12423 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12405 X0 X1
       have i₂ := eq41 X1
       grind)
    | exact superpose eq41 eq12405
    | (have j0 := eq12405 X0 X1
       grind)
    | exact resolve eq12405 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12405
  have eq12433 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12423 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq12423
    | (have j0 := eq12423 X0 X1
       grind)
    | exact resolve eq12423 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12423
  have eq12439 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12433 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12433
    | (have j0 := eq12433 X0 X1
       grind)
    | exact resolve eq12433 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12433
  have eq12441 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12439 X0 X1
       have i₂ := eq41 X1
       grind)
    | exact superpose eq41 eq12439
    | (have j0 := eq12439 X0 X1
       grind)
    | exact resolve eq12439 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12439
  have eq17898 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq362 X0 X1
       grind)
    | exact superpose eq362 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq362 X0 X1
       grind)
    | exact resolve eq13 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18105 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17898 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq17898
    | (have j0 := eq17898 X0 X1
       grind)
    | exact resolve eq17898 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17898
  have eq18250 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18105 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq18105
    | (have j0 := eq18105 X0 X1
       grind)
    | exact resolve eq18105 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18105
  have eq18251 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq18250 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18250
  have eq18349 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18251 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq18251
    | (have j0 := eq18251 X0 X1
       grind)
    | exact resolve eq18251 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18251
  have eq18381 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18349 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18349
    | (have j0 := eq18349 X0 X1
       grind)
    | exact resolve eq18349 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18349
  have eq18382 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq18381 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18381
  have eq79029 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X1)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq7397 X1 (τ X0)
       grind)
    | exact superpose eq7397 eq18
    | (have j1 := eq7397 X1 (τ X0)
       grind)
    | exact resolve eq18 eq7397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq79363 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X1)
       have i₂ := eq7397 (σ X0) X1
       grind)
    | exact superpose eq7397 eq29
    | (have j1 := eq7397 (σ X0) X1
       grind)
    | exact resolve eq29 eq7397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7397
  have eq79748 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79363 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq79363
    | (have j0 := eq79363 X0 X1
       grind)
    | exact resolve eq79363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79363
  have eq79884 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79029 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq79029
    | (have j0 := eq79029 X0 X1
       grind)
    | exact resolve eq79029 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79029
  have eq80207 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79748 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq79748
    | (have j0 := eq79748 X0 X1
       grind)
    | exact resolve eq79748 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79748
  have eq80280 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79884 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq79884
    | (have j0 := eq79884 X0 X1
       grind)
    | exact resolve eq79884 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq79884
  have eq80488 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80207 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq80207
    | (have j0 := eq80207 X0 X1
       grind)
    | exact resolve eq80207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80207
  have eq80541 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq80280 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq80280
    | (have j0 := eq80280 X0 X1
       grind)
    | exact resolve eq80280 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80280
  have eq80677 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80488 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq80488
    | (have j0 := eq80488 X0 X1
       grind)
    | exact resolve eq80488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80488
  have eq80720 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq80541 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq80541
    | (have j0 := eq80541 X0 X1
       grind)
    | exact resolve eq80541 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq80541
  have eq80778 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80677 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq80677
    | (have j0 := eq80677 X0 X1
       grind)
    | exact resolve eq80677 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80677
  have eq82401 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq80778 (σ X0) X1
       grind)
    | exact superpose eq80778 eq29
    | (have j1 := eq80778 (σ X0) X1
       grind)
    | exact resolve eq29 eq80778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80778
  have eq82731 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq82401 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq82401
    | (have j0 := eq82401 X0 X1
       grind)
    | exact resolve eq82401 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82401
  have eq83377 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq82731 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq82731
    | (have j0 := eq82731 X0 X1
       grind)
    | exact resolve eq82731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82731
  have eq98616 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80720 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq80720
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq80720 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99352 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12441 X1 X0
       have i₂ := eq80720 X0 X1
       grind)
    | exact superpose eq80720 eq12441
    | (have j0 := eq12441 X0 X1
       have j1 := eq80720 X1 X0
       grind)
    | (have r₁ := eq12441 X1 X0
       have r₂ := eq80720 X0 X1
       grind)
    | (have r₁ := eq12441 X1 X1
       have r₂ := eq80720 X1 X1
       grind)
    | exact resolve eq12441 eq80720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100028 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq80720 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80720
  have eq100077 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq99352 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99352
  have eq100324 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq98616 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98616
  have eq100856 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq100077 X0 X1
       have j1 := eq100028 X0 X1
       grind)
    | (have r₁ := eq100077 X0 X1
       have r₂ := eq100028 X0 X1
       grind)
    | (have r₁ := eq100077 X1 X0
       have r₂ := eq100028 X0 X1
       grind)
    | (have r₁ := eq100077 X1 X1
       have r₂ := eq100028 X1 X1
       grind)
    | exact resolve eq100077 eq100028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100028 eq100077
  have eq106979 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq100324 (σ X0) (σ X1)
       have i₂ := eq362 X0 X1
       grind)
    | exact superpose eq362 eq100324
    | (have j1 := eq362 X0 X1
       grind)
    | exact resolve eq100324 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq100324
  have eq108408 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq106979 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq106979
    | (have j0 := eq106979 X0 X1
       grind)
    | exact resolve eq106979 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106979
  have eq108409 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq108408 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108408
  have eq108718 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq108409 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq108409
    | (have j0 := eq108409 X0 X1
       grind)
    | exact resolve eq108409 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108409
  have eq108864 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq108718 X0 X1
       have j1 := eq18382 X0 X1
       grind)
    | (have r₁ := eq108718 X0 X1
       have r₂ := eq18382 X0 X1
       grind)
    | (have r₁ := eq108718 X1 X1
       have r₂ := eq18382 X1 X1
       grind)
    | exact resolve eq108718 eq18382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18382 eq108718
  have eq108919 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq108864 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq108864
    | (have j0 := eq108864 X0 X1
       grind)
    | exact resolve eq108864 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108864
  have eq108939 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq108919 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq108919
    | (have j0 := eq108919 X0 X1
       grind)
    | exact resolve eq108919 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108919
  have eq108953 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq108939 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq108939
    | (have j0 := eq108939 X0 X1
       grind)
    | exact resolve eq108939 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108939
  have eq118839 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq100856 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100856
    | (have j0 := eq100856 (σ X0) X1
       grind)
    | exact resolve eq100856 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100856
  have eq118907 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq118839 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq118839
    | (have j0 := eq118839 X0 X1
       grind)
    | exact resolve eq118839 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq118839
  have eq154206 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq83377 X1 (σ X0)
       grind)
    | exact superpose eq83377 eq22
    | (have j1 := eq83377 X1 (σ X0)
       grind)
    | exact resolve eq22 eq83377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83377
  have eq154217 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq154206 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq154206
    | (have j0 := eq154206 X0 X1
       grind)
    | exact resolve eq154206 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154206
  have eq154255 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq154217 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq154217
    | (have j0 := eq154217 X0 X1
       grind)
    | exact resolve eq154217 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154217
  have eq154285 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq154255 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq154255
    | (have j0 := eq154255 X0 X1
       grind)
    | exact resolve eq154255 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154255
  have eq154306 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq154285 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq154285
    | (have j0 := eq154285 X0 X1
       grind)
    | exact resolve eq154285 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154285
  have eq154318 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq154306 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq154306
    | (have j0 := eq154306 X0 X1
       grind)
    | exact resolve eq154306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154306
  have eq160929 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (k x y) ∨ (M.op y y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq154318 y x
       grind)
    | exact superpose eq154318 eq16
    | (have j1 := eq154318 y x
       grind)
    | exact resolve eq16 eq154318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154318
  have eq161420 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq160929
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq160929
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq160929 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160929
  have eq161438 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq161420
  have eq161439 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq161438
  have eq211575 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq118907 X1 (σ X0)
       grind)
    | exact superpose eq118907 eq22
    | (have j1 := eq118907 X1 (σ X0)
       grind)
    | exact resolve eq22 eq118907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq118907
  have eq211580 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq211575 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq211575
    | (have j0 := eq211575 X0 X1
       grind)
    | exact resolve eq211575 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211575
  have eq211593 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq211580 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq211580
    | (have j0 := eq211580 X0 X1
       grind)
    | exact resolve eq211580 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211580
  have eq211600 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq211593 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq211593
    | (have j0 := eq211593 X0 X1
       grind)
    | exact resolve eq211593 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211593
  have eq211604 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq211600 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq211600
    | (have j0 := eq211600 X0 X1
       grind)
    | exact resolve eq211600 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211600
  have eq211605 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq211604 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq211604
    | (have j0 := eq211604 X0 X1
       grind)
    | exact resolve eq211604 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211604
  have eq212939 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k x y) ∨ (M.op y y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq211605 y x
       grind)
    | exact superpose eq211605 eq16
    | (have j1 := eq211605 y x
       grind)
    | exact resolve eq16 eq211605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211605
  have eq473272 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7231 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7231
    | (have j0 := eq7231 (σ X0) X1
       grind)
    | exact resolve eq7231 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7231
  have eq473294 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq473272 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq473272
    | (have j0 := eq473272 X0 X1
       grind)
    | exact resolve eq473272 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473272
  have eq473299 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq473294 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq473294
    | (have j0 := eq473294 X0 X1
       grind)
    | exact resolve eq473294 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq473294
  have eq473302 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq473299 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq473299
    | (have j0 := eq473299 X0 X1
       grind)
    | exact resolve eq473299 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473299
  have eq798691 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq108953 x y
       grind)
    | exact superpose eq108953 eq16
    | (have j1 := eq108953 x y
       grind)
    | exact resolve eq16 eq108953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108953
  have eq798695 : (σ (M.op x x)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq473302 x y
       grind)
    | (have r₁ := eq798691
       have r₂ := eq473302 x y
       grind)
    | exact resolve eq798691 eq473302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473302 eq798691
  have eq809539 : (k x y) = (τ (σ (M.op x x))) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq798695
       grind)
    | exact superpose eq798695 eq10
    | exact resolve eq10 eq798695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798695
  have eq809585 : (M.op x y) = (k x y) ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq809539
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq809539
    | exact resolve eq809539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809539
  have eq820481 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq809585
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq809585
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq809585 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq820494 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by grind
  clear eq809585
  have eq820503 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq820481
  have eq820507 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j1 := eq79 x y
       grind)
    | (have r₁ := eq820503
       have r₂ := eq79 y x
       grind)
    | (have r₁ := eq820503
       have r₂ := eq79 x y
       grind)
    | exact resolve eq820503 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq820503
  have eq835910 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq12441 x y
       have i₂ := eq820507
       grind)
    | exact superpose eq820507 eq12441
    | (have j0 := eq12441 x y
       grind)
    | exact resolve eq12441 eq820507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12441 eq820507
  have eq835930 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq835910
  have eq835937 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq835930
       have r₂ := eq161439
       grind)
    | exact resolve eq835930 eq161439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161439 eq835930
  have eq844658 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq212939
       have i₂ := eq835937
       grind)
    | exact superpose eq835937 eq212939
    | exact resolve eq212939 eq835937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212939
  have eq844661 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq835937
       grind)
    | exact superpose eq835937 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq835937
       grind)
    | exact resolve eq13 eq835937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq844869 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq844658
  have eq844870 : (M.op x y) = (k x y) := by grind
  clear eq844869
  have eq852162 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1356 x y
       have i₂ := eq844870
       grind)
    | exact superpose eq844870 eq1356
    | (have j0 := eq1356 x y
       grind)
    | exact resolve eq1356 eq844870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356 eq844870
  have eq852188 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq852162
       have r₂ := eq16
       grind)
    | exact resolve eq852162 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852162
  have eq852194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq852188
       have i₂ := eq835937
       grind)
    | exact superpose eq835937 eq852188
    | exact resolve eq852188 eq835937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852188
  have eq852199 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have r₁ := eq852194
       have r₂ := eq16
       grind)
    | exact resolve eq852194 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852194
  have eq945264 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
    first
    | (have j0 := eq844661 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844661
  have eq945265 : (M.op x x) = (k x y) := by
    first
    | (have r₁ := eq945264
       have r₂ := eq820494
       grind)
    | exact resolve eq945264 eq820494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820494 eq945264
  have eq954672 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1537 x y
       have i₂ := eq945265
       grind)
    | exact superpose eq945265 eq1537
    | (have j0 := eq1537 x y
       grind)
    | exact resolve eq1537 eq945265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537 eq945265
  have eq954705 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq954672
  have eq954720 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq954705
       have i₂ := eq835937
       grind)
    | exact superpose eq835937 eq954705
    | exact resolve eq954705 eq835937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954705
  have eq954721 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq954720
       have r₂ := eq852199
       grind)
    | exact resolve eq954720 eq852199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852199 eq954720
  have eq954722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq954721
       have i₂ := eq835937
       grind)
    | exact superpose eq835937 eq954721
    | exact resolve eq954721 eq835937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835937 eq954721
  have eq954723 : False := by grind
  exact eq954723

/-- `Equation4405`: `x ◇ (x ◇ y) = (y ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation4405 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4405 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4405.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq86 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq88 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       have j1 := eq80 X0 X1
       grind)
    | (have r₁ := eq82 X0 X1
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq82 X1 X0
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq82 X1 X1
       have r₂ := eq80 X1 X1
       grind)
    | exact resolve eq82 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq82
  have eq93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq135 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0
       have i₂ := eq14 X1 (τ X0)
       grind)
    | (have i₁ := eq42 X0
       have i₂ := eq14 (τ X0) (τ X0)
       grind)
    | exact superpose eq14 eq42
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq42 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq10
    | exact resolve eq10 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq88
    | (have j0 := eq88 (σ X1) (σ X0)
       grind)
    | exact resolve eq88 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq88 X1 (τ X0)
       grind)
    | exact superpose eq88 eq17
    | (have j1 := eq88 X1 (τ X0)
       grind)
    | exact resolve eq17 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq324 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq88 (τ X0) X1
       grind)
    | exact superpose eq88 eq18
    | (have j1 := eq88 (τ X0) X1
       grind)
    | exact resolve eq18 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq339 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq312
    | (have j0 := eq312 X0 X1
       grind)
    | exact resolve eq312 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq348 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq292
    | (have j0 := eq292 X0 X1
       grind)
    | exact resolve eq292 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq357 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq339 X0 X1
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq339
    | (have j0 := eq339 X0 X1
       grind)
    | exact resolve eq339 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq339
  have eq362 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq348 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq348
    | (have j0 := eq348 X0 X1
       grind)
    | exact resolve eq348 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq1426 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq93 X1 X0
       grind)
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq93 X1 X0
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1460 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1462 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1463 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1511 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1426 X0 X1
       have j1 := eq135 X0 (σ X1)
       grind)
    | (have r₁ := eq1426 X0 X0
       have r₂ := eq135 X0 (σ X0)
       grind)
    | (have r₁ := eq1426 X0 X1
       have r₂ := eq135 X0 (σ X1)
       grind)
    | exact resolve eq1426 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq1426
  have eq1578 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1511 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq1511
    | (have j0 := eq1511 X0 X1
       grind)
    | exact resolve eq1511 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq1622 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1578 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq1578
    | (have j0 := eq1578 X0 X1
       grind)
    | exact resolve eq1578 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq1646 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1622 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1622
    | (have j0 := eq1622 X0 X1
       grind)
    | exact resolve eq1622 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622
  have eq6247 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq324 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq324
    | exact resolve eq324 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq6462 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6247 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6247
    | (have j0 := eq6247 X0 X1
       grind)
    | exact resolve eq6247 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6247
  have eq6860 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1)
       have i₂ := eq357 X1 X0
       grind)
    | exact superpose eq357 eq11
    | (have j1 := eq357 X1 X0
       grind)
    | exact resolve eq11 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6890 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq357 X0 X1
       grind)
    | exact superpose eq357 eq270
    | (have j0 := eq270 X0 X1
       have j1 := eq357 X0 X1
       grind)
    | (have r₁ := eq270 X0 X1
       have r₂ := eq357 X0 X1
       grind)
    | exact resolve eq270 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq357
  have eq7063 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6890 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6890
  have eq11790 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1646 (τ X1) (τ X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq1646
    | (have j0 := eq1646 (τ X0) (τ X1)
       grind)
    | exact resolve eq1646 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq11876 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11790 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11790
    | (have j0 := eq11790 X0 X1
       grind)
    | exact resolve eq11790 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11790
  have eq11908 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11876 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq11876
    | (have j0 := eq11876 X0 X1
       grind)
    | exact resolve eq11876 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11876
  have eq11931 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11908 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11908
    | (have j0 := eq11908 X0 X1
       grind)
    | exact resolve eq11908 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11908
  have eq11948 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11931 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq11931
    | (have j0 := eq11931 X0 X1
       grind)
    | exact resolve eq11931 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11931
  have eq11957 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11948 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11948
    | (have j0 := eq11948 X0 X1
       grind)
    | exact resolve eq11948 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11948
  have eq11962 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11957 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq11957
    | (have j0 := eq11957 X0 X1
       grind)
    | exact resolve eq11957 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11957
  have eq11963 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11962 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq11962
    | (have j0 := eq11962 X0 X1
       grind)
    | exact resolve eq11962 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11962
  have eq17389 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq362 X0 X1
       grind)
    | exact superpose eq362 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq362 X0 X1
       grind)
    | exact resolve eq13 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17593 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17389 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq17389
    | (have j0 := eq17389 X0 X1
       grind)
    | exact resolve eq17389 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17389
  have eq17742 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17593 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq17593
    | (have j0 := eq17593 X0 X1
       grind)
    | exact resolve eq17593 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17593
  have eq17743 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq17742 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17742
  have eq17843 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17743 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq17743
    | (have j0 := eq17743 X0 X1
       grind)
    | exact resolve eq17743 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17743
  have eq17879 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17843 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq17843
    | (have j0 := eq17843 X0 X1
       grind)
    | exact resolve eq17843 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17843
  have eq17880 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq17879 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17879
  have eq24562 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1460 (τ X0) (τ X1)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq1460
    | (have j0 := eq1460 (τ X1) (τ X0)
       grind)
    | exact resolve eq1460 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq24694 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24562 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq24562
    | (have j0 := eq24562 X0 X1
       grind)
    | exact resolve eq24562 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24562
  have eq24737 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24694 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq24694
    | (have j0 := eq24694 X0 X1
       grind)
    | exact resolve eq24694 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24694
  have eq24771 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24737 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24737
    | (have j0 := eq24737 X0 X1
       grind)
    | exact resolve eq24737 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24737
  have eq24798 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24771 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq24771
    | (have j0 := eq24771 X0 X1
       grind)
    | exact resolve eq24771 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24771
  have eq24823 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24798 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq24798
    | (have j0 := eq24798 X0 X1
       grind)
    | exact resolve eq24798 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24798
  have eq24845 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24823 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24823
    | (have j0 := eq24823 X0 X1
       grind)
    | exact resolve eq24823 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24823
  have eq24854 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24845 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq24845
    | (have j0 := eq24845 X0 X1
       grind)
    | exact resolve eq24845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24845
  have eq24863 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24854 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq24854
    | (have j0 := eq24854 X0 X1
       grind)
    | exact resolve eq24854 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24854
  have eq72477 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X1)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq7063 X1 (τ X0)
       grind)
    | exact superpose eq7063 eq18
    | (have j1 := eq7063 X1 (τ X0)
       grind)
    | exact resolve eq18 eq7063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq72803 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X1)
       have i₂ := eq7063 (σ X0) X1
       grind)
    | exact superpose eq7063 eq29
    | (have j1 := eq7063 (σ X0) X1
       grind)
    | exact resolve eq29 eq7063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7063
  have eq73178 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq72803 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq72803
    | (have j0 := eq72803 X0 X1
       grind)
    | exact resolve eq72803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72803
  have eq73312 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72477 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq72477
    | (have j0 := eq72477 X0 X1
       grind)
    | exact resolve eq72477 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72477
  have eq73628 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq73178 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq73178
    | (have j0 := eq73178 X0 X1
       grind)
    | exact resolve eq73178 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73178
  have eq73700 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73312 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq73312
    | (have j0 := eq73312 X0 X1
       grind)
    | exact resolve eq73312 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq73312
  have eq73903 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq73628 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq73628
    | (have j0 := eq73628 X0 X1
       grind)
    | exact resolve eq73628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73628
  have eq73956 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73700 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq73700
    | (have j0 := eq73700 X0 X1
       grind)
    | exact resolve eq73700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73700
  have eq74092 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq73903 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73903
    | (have j0 := eq73903 X0 X1
       grind)
    | exact resolve eq73903 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73903
  have eq74135 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq73956 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq73956
    | (have j0 := eq73956 X0 X1
       grind)
    | exact resolve eq73956 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq73956
  have eq74193 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq74092 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74092
    | (have j0 := eq74092 X0 X1
       grind)
    | exact resolve eq74092 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74092
  have eq77944 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq74193 (σ X0) X1
       grind)
    | exact superpose eq74193 eq29
    | (have j1 := eq74193 (σ X0) X1
       grind)
    | exact resolve eq29 eq74193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74193
  have eq78268 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77944 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq77944
    | (have j0 := eq77944 X0 X1
       grind)
    | exact resolve eq77944 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77944
  have eq78912 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78268 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq78268
    | (have j0 := eq78268 X0 X1
       grind)
    | exact resolve eq78268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78268
  have eq90716 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11963 X1 X0
       have i₂ := eq74135 X0 X1
       grind)
    | exact superpose eq74135 eq11963
    | (have j0 := eq11963 X0 X1
       have j1 := eq74135 X1 X0
       grind)
    | (have r₁ := eq11963 X1 X0
       have r₂ := eq74135 X0 X1
       grind)
    | (have r₁ := eq11963 X1 X1
       have r₂ := eq74135 X1 X1
       grind)
    | exact resolve eq11963 eq74135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90800 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq74135 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74135
  have eq90814 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq90716 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90716
  have eq90889 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq90814 X0 X1
       have j1 := eq90800 X0 X1
       grind)
    | (have r₁ := eq90814 X0 X1
       have r₂ := eq90800 X0 X1
       grind)
    | (have r₁ := eq90814 X1 X0
       have r₂ := eq90800 X0 X1
       grind)
    | (have r₁ := eq90814 X1 X1
       have r₂ := eq90800 X1 X1
       grind)
    | exact resolve eq90814 eq90800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90800 eq90814
  have eq102731 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90889 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90889
    | (have j0 := eq90889 (σ X0) X1
       grind)
    | exact resolve eq90889 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90889
  have eq102794 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq102731 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq102731
    | (have j0 := eq102731 X0 X1
       grind)
    | exact resolve eq102731 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq102731
  have eq114794 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq78912 X1 (σ X0)
       grind)
    | exact superpose eq78912 eq22
    | (have j1 := eq78912 X1 (σ X0)
       grind)
    | exact resolve eq22 eq78912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78912
  have eq114805 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq114794 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq114794
    | (have j0 := eq114794 X0 X1
       grind)
    | exact resolve eq114794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114794
  have eq114843 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq114805 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq114805
    | (have j0 := eq114805 X0 X1
       grind)
    | exact resolve eq114805 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114805
  have eq114873 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq114843 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq114843
    | (have j0 := eq114843 X0 X1
       grind)
    | exact resolve eq114843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114843
  have eq114894 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq114873 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq114873
    | (have j0 := eq114873 X0 X1
       grind)
    | exact resolve eq114873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114873
  have eq114906 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq114894 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq114894
    | (have j0 := eq114894 X0 X1
       grind)
    | exact resolve eq114894 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114894
  have eq122627 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114906 x y
       grind)
    | exact superpose eq114906 eq16
    | (have j1 := eq114906 x y
       grind)
    | exact resolve eq16 eq114906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114906
  have eq123791 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq122627
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq122627
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq122627 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123796 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq122627
       have i₂ := eq6462 x y
       grind)
    | exact superpose eq6462 eq122627
    | (have j1 := eq6462 x y
       grind)
    | (have r₁ := eq122627
       have r₂ := eq6462 x y
       grind)
    | exact resolve eq122627 eq6462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6462 eq122627
  have eq123803 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq123796
  have eq123804 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq123803
  have eq123809 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq123791
  have eq123810 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq123809
  have eq123812 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq123804
       have r₂ := eq12 y x
       grind)
    | exact resolve eq123804 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123804
  have eq126826 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq11963 y x
       have i₂ := eq123812
       grind)
    | exact superpose eq123812 eq11963
    | (have j0 := eq11963 y x
       grind)
    | (have r₁ := eq11963 y x
       have r₂ := eq123812
       grind)
    | exact resolve eq11963 eq123812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11963
  have eq126841 : (M.op x x) ≠ (M.op y y) ∨ (M.op x x) = (k y x) := by grind
  have eq126845 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
  clear eq126826
  have eq126861 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq126845
       have r₂ := eq126841
       grind)
    | exact resolve eq126845 eq126841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126841 eq126845
  have eq163729 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq102794 X1 (σ X0)
       grind)
    | exact superpose eq102794 eq22
    | (have j1 := eq102794 X1 (σ X0)
       grind)
    | exact resolve eq22 eq102794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq102794
  have eq163734 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq163729 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq163729
    | (have j0 := eq163729 X0 X1
       grind)
    | exact resolve eq163729 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163729
  have eq163747 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq163734 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq163734
    | (have j0 := eq163734 X0 X1
       grind)
    | exact resolve eq163734 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163734
  have eq163754 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq163747 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq163747
    | (have j0 := eq163747 X0 X1
       grind)
    | exact resolve eq163747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163747
  have eq163758 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq163754 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq163754
    | (have j0 := eq163754 X0 X1
       grind)
    | exact resolve eq163754 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163754
  have eq163759 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq163758 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq163758
    | (have j0 := eq163758 X0 X1
       grind)
    | exact resolve eq163758 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163758
  have eq166469 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq163759 x y
       grind)
    | exact superpose eq163759 eq16
    | (have j1 := eq163759 x y
       grind)
    | exact resolve eq16 eq163759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163759
  have eq202627 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq148 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq148
    | exact resolve eq148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq202683 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq202627 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq202627
    | (have j0 := eq202627 X0 X1
       grind)
    | exact resolve eq202627 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202627
  have eq203376 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq166469
       have i₂ := eq202683 x y
       grind)
    | exact superpose eq202683 eq166469
    | (have j1 := eq202683 x y
       grind)
    | (have r₁ := eq166469
       have r₂ := eq202683 x y
       grind)
    | exact resolve eq166469 eq202683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166469 eq202683
  have eq203451 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq203376
  have eq203452 : (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq203451
  have eq203478 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j1 := eq24863 y x
       grind)
    | (have r₁ := eq203452
       have r₂ := eq24863 y x
       grind)
    | exact resolve eq203452 eq24863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24863 eq203452
  have eq207314 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq203478
       have i₂ := eq123812
       grind)
    | exact superpose eq123812 eq203478
    | exact resolve eq203478 eq123812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123812 eq203478
  have eq207346 : (M.op x y) = (M.op y y) ∨ (M.op x x) = (k y x) := by grind
  clear eq207314
  have eq207351 : (M.op x x) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq207346
       have r₂ := eq12 y x
       grind)
    | exact resolve eq207346 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207346
  have eq211100 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1462 x y
       have i₂ := eq207351
       grind)
    | exact superpose eq207351 eq1462
    | (have j0 := eq1462 x y
       grind)
    | exact resolve eq1462 eq207351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq211101 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1463 x y
       have i₂ := eq207351
       grind)
    | exact superpose eq207351 eq1463
    | (have j0 := eq1463 x y
       grind)
    | exact resolve eq1463 eq207351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq211126 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq211101
  have eq211127 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq211100
  have eq223934 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq211126
       grind)
    | exact superpose eq211126 eq16
    | exact resolve eq16 eq211126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211126
  have eq224781 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq223934
       have i₂ := eq123810
       grind)
    | exact superpose eq123810 eq223934
    | exact resolve eq223934 eq123810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223934
  have eq224783 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq224781
  have eq229126 : (σ (M.op x x)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq224783
       have i₂ := eq362 y x
       grind)
    | exact superpose eq362 eq224783
    | (have j1 := eq362 y x
       grind)
    | exact resolve eq224783 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq229128 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq224783
       grind)
    | exact superpose eq224783 eq16
    | exact resolve eq16 eq224783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224783
  have eq229147 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (k y x)) := by
    first
    | (have j1 := eq17880 y x
       grind)
    | (have r₁ := eq229126
       have r₂ := eq17880 y x
       grind)
    | exact resolve eq229126 eq17880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17880 eq229126
  have eq229150 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq229147
       have i₂ := eq207351
       grind)
    | exact superpose eq207351 eq229147
    | exact resolve eq229147 eq207351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229147
  have eq643232 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6860 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6860
    | (have j0 := eq6860 X1 (σ X0)
       grind)
    | exact resolve eq6860 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6860
  have eq643241 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq643232 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq643232
    | (have j0 := eq643232 X0 X1
       grind)
    | exact resolve eq643232 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643232
  have eq643243 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq643241 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq643241
    | (have j0 := eq643241 X0 X1
       grind)
    | exact resolve eq643241 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq643241
  have eq643245 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq643243 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq643243
    | (have j0 := eq643243 X0 X1
       grind)
    | exact resolve eq643243 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643243
  have eq644353 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq643245 y x
       have i₂ := eq126861
       grind)
    | exact superpose eq126861 eq643245
    | (have j0 := eq643245 y x
       grind)
    | exact resolve eq643245 eq126861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126861 eq643245
  have eq644374 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq644353
  have eq2618582 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq229150
       grind)
    | exact superpose eq229150 eq16
    | exact resolve eq16 eq229150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229150
  have eq2618583 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2618582
       have r₂ := eq644374
       grind)
    | exact resolve eq2618582 eq644374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644374 eq2618582
  have eq2635857 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2618583
       have i₂ := eq123810
       grind)
    | exact superpose eq123810 eq2618583
    | exact resolve eq2618583 eq123810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123810 eq2618583
  have eq2635884 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq2635857
  have eq2635903 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2635884
       have r₂ := eq229128
       grind)
    | exact resolve eq2635884 eq229128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229128 eq2635884
  have eq2652384 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2635903
       grind)
    | exact superpose eq2635903 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2635903
       grind)
    | exact resolve eq13 eq2635903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2652420 : (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by grind
  clear eq2652384
  have eq2652425 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq2652420
       have i₂ := eq207351
       grind)
    | exact superpose eq207351 eq2652420
    | exact resolve eq2652420 eq207351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207351 eq2652420
  have eq2652426 : (M.op x x) = (M.op y y) := by grind
  clear eq2652425
  have eq2670993 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq211127
       have i₂ := eq2652426
       grind)
    | exact superpose eq2652426 eq211127
    | exact resolve eq211127 eq2652426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211127 eq2652426
  have eq2671252 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2670993
  have eq2688887 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2671252
       grind)
    | exact superpose eq2671252 eq16
    | exact resolve eq16 eq2671252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671252
  have eq2688922 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2688887
       have i₂ := eq2635903
       grind)
    | exact superpose eq2635903 eq2688887
    | exact resolve eq2688887 eq2635903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635903 eq2688887
  have eq2688923 : False := by grind
  exact eq2688923

/-- `Equation4408`: `x ◇ (x ◇ y) = (y ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_y_pxy_Equation4408 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4408 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4408.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq69 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq83 (σ X1) (σ X0)
       grind)
    | exact superpose eq83 eq15
    | (have j1 := eq83 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq83 X1 (τ X0)
       grind)
    | exact superpose eq83 eq19
    | (have j1 := eq83 X1 (τ X0)
       grind)
    | exact resolve eq19 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq113 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq83
  have eq158 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq113 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq159 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq158 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq198 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq159 (σ X0)
       grind)
    | exact superpose eq159 eq15
    | exact resolve eq15 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq198 X0
       have i₂ := eq159 X0
       grind)
    | exact superpose eq159 eq198
    | exact resolve eq198 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq198
  have eq327 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq209 X0
       grind)
    | exact superpose eq209 eq9
    | exact resolve eq9 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq342 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq330 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq330
    | exact resolve eq330 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq347 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq342
  have eq2526 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq105 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq2646 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2526 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2526
    | (have j0 := eq2526 X0 X1
       grind)
    | exact resolve eq2526 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526
  have eq4186 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq103 X1 X0
       grind)
    | exact superpose eq103 eq10
    | (have j1 := eq103 X1 X0
       grind)
    | exact resolve eq10 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq4325 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4186 X0 X1
       have i₂ := eq209 X0
       grind)
    | exact superpose eq209 eq4186
    | (have j0 := eq4186 X0 X1
       grind)
    | exact resolve eq4186 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4186
  have eq4444 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4325 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4325
    | (have j0 := eq4325 X0 X1
       grind)
    | exact resolve eq4325 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4325
  have eq4696 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4444 y x
       grind)
    | exact superpose eq4444 eq16
    | (have j1 := eq4444 y x
       grind)
    | exact resolve eq16 eq4444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4444
  have eq4780 : x = (M.op y y) := by
    first
    | (have j1 := eq2646 x y
       grind)
    | (have r₁ := eq4696
       have r₂ := eq2646 x y
       grind)
    | exact resolve eq4696 eq2646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646 eq4696
  have eq5057 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq4780
       grind)
    | exact superpose eq4780 eq9
    | exact resolve eq9 eq4780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5074 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq327 y X0
       have i₂ := eq4780
       grind)
    | exact superpose eq4780 eq327
    | exact resolve eq327 eq4780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq4780
  have eq8981 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq5074 (σ y)
       have i₂ := eq209 y
       grind)
    | exact superpose eq209 eq5074
    | exact resolve eq5074 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq5074
  have eq9039 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq8981
       have i₂ := eq347 y
       grind)
    | exact superpose eq347 eq8981
    | exact resolve eq8981 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq8981
  have eq9052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9039
       have i₂ := eq5057 y
       grind)
    | exact superpose eq5057 eq9039
    | exact resolve eq9039 eq5057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5057 eq9039
  have eq9059 : False := by grind
  exact eq9059

/-- `Equation4408`: `x ◇ (x ◇ y) = (y ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_y_pyx_Equation4408 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4408 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4408.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq533 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq69 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq540 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq533 X0 X1
       have j1 := eq67 X1 X0
       grind)
    | (have r₁ := eq533 X0 X0
       have r₂ := eq67 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq533 X0 X1
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq533 X1 X0
       have r₂ := eq67 X0 X1
       grind)
    | exact resolve eq533 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq533
  have eq575 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq1024 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq575 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq1025 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1024 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1181 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1025 (σ X0)
       grind)
    | exact superpose eq1025 eq15
    | exact resolve eq15 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1192 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1181 X0
       have i₂ := eq1025 X0
       grind)
    | exact superpose eq1025 eq1181
    | exact resolve eq1181 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025 eq1181
  have eq1868 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq1885 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq540 X1 (σ X0)
       have i₂ := eq1192 X0
       grind)
    | exact superpose eq1192 eq540
    | (have j0 := eq540 X1 (σ X0)
       grind)
    | exact resolve eq540 eq1192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1891 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1868 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq1868
    | exact resolve eq1868 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868
  have eq1899 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq1891
  have eq5475 : ∀ X0 X1 : G, (M.op X1 X1) = (τ X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1885 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1885 X0 (σ X0)
       grind)
    | exact superpose eq1885 eq10
    | (have j1 := eq1885 X1 X0
       grind)
    | exact resolve eq10 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq7759 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq5475 (σ X1) X0
       grind)
    | exact superpose eq5475 eq15
    | (have j1 := eq5475 (σ X1) X0
       grind)
    | exact resolve eq15 eq5475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5475
  have eq7783 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7759 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7759
    | (have j0 := eq7759 X0 X1
       grind)
    | exact resolve eq7759 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7759
  have eq10599 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7783 x y
       grind)
    | exact superpose eq7783 eq16
    | (have j1 := eq7783 x y
       grind)
    | exact resolve eq16 eq7783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7783
  have eq11317 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10599
       have i₂ := eq540 y x
       grind)
    | exact superpose eq540 eq10599
    | (have j1 := eq540 y x
       grind)
    | exact resolve eq10599 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq10599
  have eq11326 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq11317
  have eq11327 : y = (M.op x x) := by grind
  clear eq11326
  have eq11513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1899 x
       have i₂ := eq11327
       grind)
    | exact superpose eq11327 eq1899
    | exact resolve eq1899 eq11327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899 eq11327
  have eq11542 : False := by grind
  exact eq11542
