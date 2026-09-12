import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pyy_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq44 (k X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq44 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq35 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq46 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq47 X1 X0
       grind)
    | (have r₁ := eq52 X1 X0
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq52 X0 (M.op X1 X1)
       have r₂ := eq47 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq52 X0 X1
       have r₂ := eq47 (k X0 X1) X1
       grind)
    | exact resolve eq52 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq52
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq56
    | (have j0 := eq56 X0 X1
       grind)
    | exact resolve eq56 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq66 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq57
  have eq68 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq66 X0 X1
       have r₂ := eq65 X0 X1
       grind)
    | exact resolve eq66 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq66
  have eq166 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq262 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X0) X3 X4
       have i₂ := eq19 X0 X1 X2
       grind)
    | (have i₁ := eq9 (M.op X2 X2) X1 X2
       have i₂ := eq19 X2 X2 X2
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2707 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq262 X1 X1 X2 X3 X4
       have i₂ := eq68 X0 X1
       grind)
    | (have i₁ := eq262 X0 X1 X2 X3 X4
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq262
    | (have j1 := eq68 X0 X1
       grind)
    | exact resolve eq262 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq2831 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) ≠ (M.op X0 X5) ∨ (M.op X0 X5) = (k X5 X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq166 X5 X0
       have i₂ := eq262 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq262 eq166
    | (have j0 := eq166 X5 X0
       grind)
    | exact resolve eq166 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq262
  have eq3020 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2707 X0 X1 x x x
       have j1 := eq2831 X0 X1 x x x X1
       grind)
    | (have r₁ := eq2707 X0 X1 x x x
       have r₂ := eq2831 X0 X1 x x x X1
       grind)
    | exact resolve eq2707 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707 eq2831
  have eq83028 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3020 (σ X0) (σ X1)
       grind)
    | exact superpose eq3020 eq15
    | exact resolve eq15 eq3020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83050 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83028 X0 X1
       have i₂ := eq3020 X0 X1
       grind)
    | exact superpose eq3020 eq83028
    | exact resolve eq83028 eq3020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3020 eq83028
  have eq83077 : False := by grind
  exact eq83077

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X2 X1) = X2 ∨ (M.op X0 X0) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X2
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X2 X1) = X2 ∨ (M.op X0 X0) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq36 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X0 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq36 (k X1 X2) X1 X2
       have r₂ := eq12 (k X1 X2) (k X1 X2)
       grind)
    | (have r₁ := eq36 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq107 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X0 X0) X2) X3)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq20 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq122 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X0 X0) X2) X3)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq107 X0 X1 X2 X3
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq107 X0 (M.op X0 X0) X2 X3
       have r₂ := eq12 (M.op (M.op (M.op X0 X0) X2) X3) (M.op X0 X0)
       grind)
    | (have r₁ := eq107 X1 X0 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq107 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X3 (M.op X0 X0)
       have i₂ := eq19 X0 X1 X2
       grind)
    | (have i₁ := eq21 X1 X1 (M.op X1 X2)
       have i₂ := eq19 X1 X1 X2
       grind)
    | exact superpose eq19 eq21
    | exact resolve eq21 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21
  have eq1191 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1192 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1191 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1191 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1191 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq2249 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1192 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq5305 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 X1 (M.op (M.op x x) (M.op x x)) x
       have i₂ := eq178 x x x X0
       grind)
    | exact superpose eq178 eq122
    | (have j0 := eq122 X0 X1 x x
       grind)
    | exact resolve eq122 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq178
  have eq5495 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5305 X0 X1
       have j1 := eq2249 X1 X0
       grind)
    | (have r₁ := eq5305 X1 X1
       have r₂ := eq2249 X1 X1
       grind)
    | (have r₁ := eq5305 X1 X0
       have r₂ := eq2249 X0 X1
       grind)
    | exact resolve eq5305 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2249 eq5305
  have eq7332 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq5495 (σ X1) (σ X0)
       grind)
    | exact superpose eq5495 eq15
    | exact resolve eq15 eq5495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7347 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7332 X0 X1
       have i₂ := eq5495 X1 X0
       grind)
    | exact superpose eq5495 eq7332
    | exact resolve eq7332 eq5495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5495 eq7332
  have eq7361 : False := by grind
  exact eq7361

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pyx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq538 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq528 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq544 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq538 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq538 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq538 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq538 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq545 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq527 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq527 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq527 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq554 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq544
    | (have j0 := eq544 X0 X1
       grind)
    | exact resolve eq544 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq555 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq554 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq556 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq545 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq545
    | (have j0 := eq545 X0 X1
       grind)
    | exact resolve eq545 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq557 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq556 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq562 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq557 X0 X1
       have j1 := eq555 X0 X1
       grind)
    | (have r₁ := eq557 X0 X1
       have r₂ := eq555 X0 X1
       grind)
    | exact resolve eq557 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq557
  have eq563 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq562 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq562
    | exact resolve eq562 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq562 x y
       grind)
    | exact superpose eq562 eq16
    | exact resolve eq16 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq688 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq563 X0 (τ X1)
       grind)
    | exact superpose eq563 eq18
    | exact resolve eq18 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq563
  have eq711 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq688 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq688
    | exact resolve eq688 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq722 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq711 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq711
    | exact resolve eq711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq749 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq574
       have i₂ := eq722 x y
       grind)
    | exact superpose eq722 eq574
    | exact resolve eq574 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq722
  have eq750 : False := by grind
  exact eq750

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
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
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq44 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq47 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq47 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq51
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       have j1 := eq48 X0 X1
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq57 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq57
  have eq199 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq204 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       have j1 := eq61 X1 X0
       grind)
    | (have r₁ := eq199 X1 X1
       have r₂ := eq61 X1 X1
       grind)
    | (have r₁ := eq199 X1 X0
       have r₂ := eq61 X0 X1
       grind)
    | exact resolve eq199 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq199
  have eq269 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq204 (σ X1) (σ X0)
       grind)
    | exact superpose eq204 eq15
    | exact resolve eq15 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq269 X0 X1
       have i₂ := eq204 X1 X0
       grind)
    | exact superpose eq204 eq269
    | exact resolve eq269 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq269
  have eq276 : False := by grind
  exact eq276

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq25 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq27 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
  have eq110 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq25 (τ X0)
       grind)
    | exact superpose eq25 eq19
    | (have j1 := eq25 (τ X0)
       grind)
    | exact resolve eq19 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq25
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq110
    | (have j0 := eq110 X0
       grind)
    | exact resolve eq110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq118 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
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
  have eq122 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq118 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq118 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq118 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq127 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq27
    | (have j0 := eq27 X0 X1
       have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq27 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq122 (σ X0)
       grind)
    | exact superpose eq122 eq15
    | exact resolve eq15 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq148 X0
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq148
    | exact resolve eq148 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq148
  have eq883 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30
    | exact resolve eq30 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq899 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq883 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq883
    | (have j0 := eq883 X0 X1
       grind)
    | exact resolve eq883 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq2162 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq127 x y
       grind)
    | exact superpose eq127 eq16
    | (have j1 := eq127 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq127 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq127 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq127 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq2192 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2162
  have eq2270 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2192
       grind)
    | exact superpose eq2192 eq16
    | exact resolve eq16 eq2192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2272 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2192
       grind)
    | exact superpose eq2192 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2192
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2192
       grind)
    | exact resolve eq12 eq2192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2192
  have eq2290 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2272
  have eq2299 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2290
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2290
    | exact resolve eq2290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq4550 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq899 y x
       have i₂ := eq2299
       grind)
    | exact superpose eq2299 eq899
    | (have j0 := eq899 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq899 eq2299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq2299
  have eq4577 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq4550
  have eq4593 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4577
       have r₂ := eq2270
       grind)
    | exact resolve eq4577 eq2270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270 eq4577
  have eq6965 : x ≠ x ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq4593
       grind)
    | exact superpose eq4593 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq4593
       grind)
    | exact resolve eq12 eq4593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6994 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6965
  have eq13969 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq27 x y
       have i₂ := eq6994
       grind)
    | exact superpose eq6994 eq27
    | (have j0 := eq27 x y
       grind)
    | exact resolve eq27 eq6994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6994
  have eq13972 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13969
  have eq28185 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq13972
       grind)
    | exact superpose eq13972 eq16
    | exact resolve eq16 eq13972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13972
  have eq36192 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28185
       have i₂ := eq4593
       grind)
    | exact superpose eq4593 eq28185
    | exact resolve eq28185 eq4593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4593 eq28185
  have eq36193 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq36192
  have eq36194 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq36193
  have eq59242 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq36194
       grind)
    | exact superpose eq36194 eq10
    | exact resolve eq10 eq36194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36194
  have eq59301 : x = y ∨ x = y := by
    first
    | (have i₁ := eq59242
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq59242
    | exact resolve eq59242 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59242
  have eq59302 : x = y := by grind
  clear eq59301
  have eq73667 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59302
       grind)
    | exact superpose eq59302 eq16
    | exact resolve eq16 eq59302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59302
  have eq73668 : False := by grind
  exact eq73668

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X1 X1) X2)) X1) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X1) X2) (M.op X2 x)
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = (M.op (M.op X1 X4) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq30 X1 X4 X3
       have i₂ := eq30 X1 X2 X0
       grind)
    | (have i₁ := eq30 X2 X1 X2
       have i₂ := eq30 X2 X2 X2
       grind)
    | exact superpose eq30 eq30
    | exact resolve eq30 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X1 X2) (M.op X2 X0))) X1) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32 X1 (M.op X1 X1) X3
       have i₂ := eq30 X1 X2 X0
       grind)
    | (have i₁ := eq32 X1 (M.op X1 X2) X3
       have i₂ := eq30 X1 X1 X2
       grind)
    | exact superpose eq30 eq32
    | exact resolve eq32 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32
  have eq196 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq226 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq226 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq245 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq244 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq248 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq578 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 x X1 X2 (M.op X1 X2)
       have i₂ := eq74 (M.op X2 x) (M.op X1 X2) (M.op X1 X2) X3 X0
       grind)
    | (have i₁ := eq87 x X1 X2 (M.op X1 X2)
       have i₂ := eq74 X3 (M.op X1 X2) X0 (M.op X2 x) (M.op X1 X2)
       grind)
    | exact superpose eq74 eq87
    | exact resolve eq87 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq87
  have eq730 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq245
  have eq829 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq730 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq908 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq829 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq3135 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X2) (M.op X2 X3)) X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq578 X0 X0 X0 X3
       have i₂ := eq248 X0 X1
       grind)
    | (have i₁ := eq578 X0 X1 X0 X3
       have i₂ := eq248 X0 X1
       grind)
    | exact superpose eq248 eq578
    | (have j1 := eq248 X0 X1
       grind)
    | exact resolve eq578 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq578
  have eq3296 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3135 X0 X1 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq3135
    | (have j0 := eq3135 X0 X1 x x
       grind)
    | exact resolve eq3135 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135
  have eq3298 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3296 X0 X1
       have j1 := eq908 X0 X1
       grind)
    | (have r₁ := eq3296 X0 X1
       have r₂ := eq908 X0 X1
       grind)
    | (have r₁ := eq3296 X1 X1
       have r₂ := eq908 X1 X1
       grind)
    | exact resolve eq3296 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908 eq3296
  have eq3316 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3298 (σ X0) (σ X1)
       grind)
    | exact superpose eq3298 eq15
    | exact resolve eq15 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3329 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3316 X0 X1
       have i₂ := eq3298 X0 X1
       grind)
    | exact superpose eq3298 eq3316
    | exact resolve eq3316 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3298 eq3316
  have eq3462 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3329 x y
       grind)
    | exact superpose eq3329 eq16
    | (have r₁ := eq16
       have r₂ := eq3329 x y
       grind)
    | exact resolve eq16 eq3329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3329
  have eq3484 : False := by grind
  exact eq3484

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_pyx_pxy_y_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
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
  clear eq43
  have eq52 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
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
  have eq85 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq44
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq44 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq124 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124
    | exact resolve eq124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq522 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq125 eq85
    | (have j0 := eq85 (σ x) (σ y)
       grind)
    | exact resolve eq85 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq125
  have eq774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq773
    | exact resolve eq773 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq777 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq774
       have r₂ := eq27
       grind)
    | exact resolve eq774 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq779 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq777
    | exact resolve eq777 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq787 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq779 eq54
    | exact resolve eq54 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq790 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ x)) X0) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq779 eq14
    | exact resolve eq14 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq522 X0 X2
       have i₂ := eq522 X0 X1
       grind)
    | (have i₁ := eq522 X1 X1
       have i₂ := eq522 X1 X1
       grind)
    | exact superpose eq522 eq522
    | exact resolve eq522 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1107 : (M.op (M.op x y) x) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq522 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq522
    | (have j0 := eq522 x y
       grind)
    | exact resolve eq522 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1111 : ∀ X0 : G, y = (M.op (M.op (M.op y X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 y
       have i₂ := eq522 y X0
       grind)
    | (have i₁ := eq52 y
       have i₂ := eq522 y y
       grind)
    | exact superpose eq522 eq52
    | exact resolve eq52 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1113 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq790 sF2
       have i₂ := eq522 sF2 x
       grind)
    | (have i₁ := eq790 sF2
       have i₂ := eq522 sF2 sF2
       grind)
    | exact superpose eq522 eq790
    | exact resolve eq790 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq1114 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq53 sF3
       have i₂ := eq522 sF3 x
       grind)
    | (have i₁ := eq53 sF3
       have i₂ := eq522 sF3 sF3
       grind)
    | exact superpose eq522 eq53
    | exact resolve eq53 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1115 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq787 sF4
       have i₂ := eq522 sF4 x
       grind)
    | (have i₁ := eq787 sF4
       have i₂ := eq522 sF4 sF4
       grind)
    | exact superpose eq522 eq787
    | exact resolve eq787 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq787
  have eq1144 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq1113
    | (have j0 := eq1113 (σ y)
       grind)
    | exact resolve eq1113 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1163 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1144 eq1115
    | exact resolve eq1115 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq1144
  have eq1173 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq1163
  have eq1187 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1173 eq14
    | exact resolve eq14 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq19040 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq779 eq1114
    | exact resolve eq1114 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq1114
  have eq25665 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq19040 eq1187
    | exact resolve eq1187 eq19040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187 eq19040
  have eq25697 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq25665
  have eq25781 : y = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1111 x
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq1111
    | exact resolve eq1111 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq25788 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq14
    | exact resolve eq14 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25697
  have eq26000 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq25781
       have i₂ := eq1102 sF0 y x
       grind)
    | (have i₁ := eq25781
       have i₂ := eq1102 sF0 x y
       grind)
    | exact superpose eq1102 eq25781
    | exact resolve eq25781 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq25781
  have eq31029 : x = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25788 x
       have i₂ := eq1107
       grind)
    | exact superpose eq1107 eq25788
    | exact resolve eq25788 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107 eq25788
  have eq31106 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31029 eq26000
    | exact resolve eq26000 eq31029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26000 eq31029
  have eq31139 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq31106
  have eq31223 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq31139 eq29
    | exact resolve eq29 eq31139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq31139
  have eq31302 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq31223
    | exact resolve eq31223 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq31223
  have eq31303 : x = y := by grind
  clear eq31302
  have eq31306 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq31303
       grind)
    | exact superpose eq31303 eq18
    | exact resolve eq18 eq31303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq31307 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq31303
       grind)
    | exact superpose eq31303 eq24
    | exact resolve eq24 eq31303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq31303
  have eq31430 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq31307
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31307
    | exact resolve eq31307 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31307
  have eq31442 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31430 eq26
    | exact resolve eq26 eq31430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq31430
  have eq31679 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31442 eq71
    | exact resolve eq71 eq31442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq31442
  have eq31762 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq31679
       have i₂ := eq31306
       grind)
    | exact superpose eq31306 eq31679
    | exact resolve eq31679 eq31306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31306 eq31679
  have eq31777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31762 eq15
    | exact resolve eq15 eq31762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31762
  have eq31821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq31777
    | exact resolve eq31777 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq31777
  have eq31836 : False := by grind
  exact eq31836

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_pxy_y_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op (M.op X1 X1) X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
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
  have eq177 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (k (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X0) X1) (M.op X2 X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) := by
    intro X0
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X0
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (k X0 X1)) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X0) (M.op X2 X0)) ∨ (k (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 (M.op (M.op X0 X0) X1) (M.op X2 X0)
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 (M.op (M.op X0 X0) X1) (M.op X2 X0)
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : (M.op x y) = (k x y) ∨ x = (M.op y y) := by
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
  have eq581 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq586 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq578
       grind)
    | exact superpose eq578 eq41
    | exact resolve eq41 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq587 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq586
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq586
    | exact resolve eq586 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq589 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq587
    | exact resolve eq587 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq599 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq589 eq581
    | exact resolve eq581 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq589
  have eq606 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq599
       have r₂ := eq27
       grind)
    | exact resolve eq599 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq614 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq606 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq606 eq13
    | exact resolve eq13 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq617 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq614
       have r₂ := eq615
       grind)
    | exact resolve eq614 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq615
  have eq619 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq617 eq116
    | exact resolve eq116 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq617
  have eq626 : x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq619
    | exact resolve eq619 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq977 : ∀ X0 X1 : G, y = (M.op (M.op x X0) (M.op X1 y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq564 y X0 X1
       have i₂ := eq626
       grind)
    | exact superpose eq626 eq564
    | (have j0 := eq564 y X1 x
       grind)
    | exact resolve eq564 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1028 : ∀ X0 X1 : G, y = (M.op (M.op x X0) (M.op X1 y)) ∨ y = (M.op y y) ∨ x = (k y y) := by
    intro X0 X1
    first
    | exact superpose eq28 eq977
    | (have j0 := eq977 X0 X1
       have j1 := eq28 y y
       grind)
    | exact resolve eq977 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1030 : ∀ X0 X1 : G, y = (M.op (M.op x X0) (M.op X1 y)) ∨ x = y ∨ x = (k y y) := by
    intro X0 X1
    first
    | exact superpose eq626 eq1028
    | (have j0 := eq1028 X0 X1
       grind)
    | exact resolve eq1028 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1063 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq565 y y X0
       have i₂ := eq626
       grind)
    | exact superpose eq626 eq565
    | (have j0 := eq565 y y x
       grind)
    | exact resolve eq565 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1081 : ∀ X0 : G, y = (M.op (M.op (k y y) X0) x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq28 eq1063
    | (have j1 := eq28 y y
       grind)
    | exact resolve eq1063 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1090 : ∀ X0 : G, y = (M.op (M.op (k y y) X0) x) ∨ y = (M.op y y) ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq28 eq1081
    | (have j0 := eq1081 X0
       have j1 := eq28 y y
       grind)
    | exact resolve eq1081 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1081
  have eq1093 : ∀ X0 : G, y = (M.op (M.op (k y y) X0) x) ∨ x = y ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq626 eq1090
    | (have j0 := eq1090 X0
       grind)
    | exact resolve eq1090 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1313 : ∀ X1 : G, y = (M.op (M.op (M.op y y) X1) x) ∨ x = y ∨ x = (k y y) := by
    intro X1
    first
    | (have i₁ := eq179 x (M.op (k y y) x) x
       have i₂ := eq1093 x
       grind)
    | exact superpose eq1093 eq179
    | exact resolve eq179 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq1093
  have eq1318 : ∀ X1 : G, y = (M.op (M.op x X1) x) ∨ x = y ∨ x = (k y y) := by
    intro X1
    first
    | exact superpose eq626 eq1313
    | exact resolve eq1313 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq1313
  have eq3093 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X0 ∨ (k (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 (M.op X0 X0)
       have i₂ := eq573 X0 X1 (M.op X0 X0)
       grind)
    | (have i₁ := eq16 X0 (M.op X0 X0) x
       have i₂ := eq573 (M.op X0 X0) (M.op x X0) x
       grind)
    | exact superpose eq573 eq16
    | (have j1 := eq573 X0 X1 (M.op X0 X0)
       grind)
    | exact resolve eq16 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq3151 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3093 X0 X1
       have j1 := eq182 X0 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq3093 X0 X1
       have r₂ := eq182 X0 X1 x
       grind)
    | exact resolve eq3093 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq3093
  have eq4065 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3151 (M.op X0 X0) (M.op x X0)
       have i₂ := eq16 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq16 eq3151
    | exact resolve eq3151 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4067 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq185 eq3151
    | exact resolve eq3151 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq4070 : (M.op y y) = (k y (M.op (M.op (M.op y y) (M.op y y)) (M.op y y))) := by
    first
    | exact superpose eq177 eq3151
    | exact resolve eq3151 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq4073 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq178 eq3151
    | exact resolve eq3151 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq4084 : x = (k y y) ∨ x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq3151 x x
       have i₂ := eq1318 x
       grind)
    | exact superpose eq1318 eq3151
    | exact resolve eq3151 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318 eq3151
  have eq4149 : x = (k y y) ∨ x = y := by grind
  clear eq4084
  have eq4184 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4073
       have i₂ := eq16 sF3 (M.op sF3 sF3) sF3
       grind)
    | exact superpose eq16 eq4073
    | exact resolve eq4073 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4073
  have eq4187 : (k y y) = (M.op y y) := by
    first
    | (have i₁ := eq4070
       have i₂ := eq16 y (M.op y y) y
       grind)
    | exact superpose eq16 eq4070
    | exact resolve eq4070 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4070
  have eq4190 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq4067
       have i₂ := eq16 sF0 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq16 eq4067
    | exact resolve eq4067 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4067
  have eq4192 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4065 X0
       have i₂ := eq16 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq16 eq4065
    | exact resolve eq4065 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4065
  have eq4248 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq4149
       grind)
    | exact superpose eq4149 eq41
    | exact resolve eq41 eq4149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq4250 : ∀ X0 X1 : G, y = (M.op (M.op x X0) (M.op X1 y)) ∨ y = (M.op y y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq564 y X0 X1
       have i₂ := eq4149
       grind)
    | exact superpose eq4149 eq564
    | (have j0 := eq564 y X1 x
       grind)
    | exact resolve eq564 eq4149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq4149
  have eq4254 : ∀ X0 X1 : G, y = (k y y) ∨ y = (M.op (M.op x X0) (M.op X1 y)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq4250 X0 X1
       have i₂ := eq4187
       grind)
    | exact superpose eq4187 eq4250
    | (have j0 := eq4250 X0 X1
       grind)
    | exact resolve eq4250 eq4187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4187 eq4250
  have eq4256 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4248
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4248
    | exact resolve eq4248 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4248
  have eq4259 : ∀ X0 X1 : G, x = y ∨ y = (M.op (M.op x X0) (M.op X1 y)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1030 eq4254
    | (have j0 := eq4254 X0 X1
       have j1 := eq1030 X0 X1
       grind)
    | exact resolve eq4254 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030 eq4254
  have eq4260 : ∀ X0 X1 : G, y = (M.op (M.op x X0) (M.op X1 y)) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq4259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4259
  have eq4263 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4256
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4256
    | exact resolve eq4256 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4256
  have eq4277 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ y)) X0) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4263 eq565
    | (have j0 := eq565 (σ y) (σ y) x
       grind)
    | exact resolve eq565 eq4263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4278 : ∀ X0 : G, (σ y) = (M.op (M.op (k (σ y) (σ y)) X0) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4184 eq4277
    | exact resolve eq4277 eq4184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4277
  have eq4285 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (k (σ y) (σ y)) X0) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4184 eq4278
    | (have j0 := eq4278 X0
       grind)
    | exact resolve eq4278 eq4184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4184 eq4278
  have eq4291 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op (M.op (k (σ y) (σ y)) X0) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4263 eq4285
    | (have j0 := eq4285 X0
       grind)
    | exact resolve eq4285 eq4263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4285
  have eq4292 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4263 eq4291
    | exact resolve eq4291 eq4263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4291
  have eq4668 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4260 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4260
    | (have j0 := eq4260 y X0
       grind)
    | exact resolve eq4260 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4260
  have eq4780 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq4668 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4668
    | (have j0 := eq4668 x
       grind)
    | exact resolve eq4668 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4668
  have eq4798 : y = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq4190 eq4780
    | exact resolve eq4780 eq4190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4190 eq4780
  have eq4806 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq4798 eq42
    | exact resolve eq42 eq4798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq4798
  have eq4813 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq4806
    | exact resolve eq4806 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4806
  have eq4815 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq4813
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4813
    | exact resolve eq4813 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4813
  have eq4823 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4815 eq565
    | (have j0 := eq565 (σ (M.op x y)) (σ (M.op x y)) x
       grind)
    | exact resolve eq565 eq4815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq4824 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) X0) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4823 X0
       have i₂ := eq4192 sF1
       grind)
    | exact superpose eq4192 eq4823
    | exact resolve eq4823 eq4192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4823
  have eq4831 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) X0) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4824 X0
       have i₂ := eq4192 sF1
       grind)
    | exact superpose eq4192 eq4824
    | (have j0 := eq4824 X0
       grind)
    | exact resolve eq4824 eq4192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4824
  have eq4837 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) X0) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4815 eq4831
    | (have j0 := eq4831 X0
       grind)
    | exact resolve eq4831 eq4815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4831
  have eq4838 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4815 eq4837
    | exact resolve eq4837 eq4815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4837
  have eq5801 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4292 eq16
    | exact resolve eq16 eq4292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4292
  have eq6279 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5801 eq4838
    | exact resolve eq4838 eq5801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4838 eq5801
  have eq6312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6279
  have eq6332 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq6312
    | exact resolve eq6312 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6312
  have eq6350 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq6332
       have r₂ := eq27
       grind)
    | exact resolve eq6332 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6332
  have eq6372 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6350 eq32
    | exact resolve eq32 eq6350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6350
  have eq6483 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30 eq6372
    | exact resolve eq6372 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6372
  have eq6484 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq6483
  have eq6507 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq6484 eq4815
    | exact resolve eq4815 eq6484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4815 eq6484
  have eq6513 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq6507
  have eq6520 : (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4263 eq6513
    | exact resolve eq6513 eq4263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4263 eq6513
  have eq6541 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq6520 eq32
    | exact resolve eq32 eq6520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq6520
  have eq6653 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq6541
    | exact resolve eq6541 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq6541
  have eq6654 : x = y := by grind
  clear eq6653
  have eq6672 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6654
       grind)
    | exact superpose eq6654 eq18
    | exact resolve eq18 eq6654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6673 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6654
       grind)
    | exact superpose eq6654 eq24
    | exact resolve eq24 eq6654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq6654
  have eq6742 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq6673
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6673
    | exact resolve eq6673 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6673
  have eq6743 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq6672
       have i₂ := eq4192 x
       grind)
    | exact superpose eq4192 eq6672
    | exact resolve eq6672 eq4192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6672
  have eq6756 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6742 eq26
    | exact resolve eq26 eq6742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6742
  have eq6869 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6756
       have i₂ := eq4192 sF2
       grind)
    | exact superpose eq4192 eq6756
    | exact resolve eq6756 eq4192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4192 eq6756
  have eq6976 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq6743
       grind)
    | exact superpose eq6743 eq40
    | exact resolve eq40 eq6743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq6743
  have eq6985 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6976
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6976
    | exact resolve eq6976 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6976
  have eq6992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6869 eq6985
    | exact resolve eq6985 eq6869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6869 eq6985
  have eq6998 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq6992
    | exact resolve eq6992 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6992
  have eq7004 : False := by grind
  exact eq7004
