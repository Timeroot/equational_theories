import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3071`: `x = (((x ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation3071 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3071 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3071.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq33 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq33 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq37 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq44
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq50 X0 X1
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq50 X0 X1
       grind)
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq51
  have eq105 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq109 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       have j1 := eq53 X0 X1
       grind)
    | (have r₁ := eq105 X0 X1
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq105 X0 X0
       have r₂ := eq53 X0 X0
       grind)
    | exact resolve eq105 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq105
  have eq238 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq109 (σ X0) (σ X1)
       grind)
    | exact superpose eq109 eq15
    | exact resolve eq15 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq238 X0 X1
       have i₂ := eq109 X0 X1
       grind)
    | exact superpose eq109 eq238
    | exact resolve eq238 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq238
  have eq247 : False := by grind
  exact eq247

/-- `Equation3071`: `x = (((x ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_pxx_pxy_Equation3071 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3071 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3071.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq273 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq273
    | (have j0 := eq273 (σ X0) (σ X1)
       grind)
    | exact resolve eq273 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq273 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq273
    | (have j0 := eq273 (τ X0) (τ X1)
       grind)
    | exact resolve eq273 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq274 X0 X1
       have i₂ := eq273 X0 X1
       grind)
    | exact superpose eq273 eq274
    | (have j0 := eq274 X0 X1
       have j1 := eq273 (σ X0) (σ X1)
       grind)
    | exact resolve eq274 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq679 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) (τ X0)
       have i₂ := eq275 X0 X1
       grind)
    | exact superpose eq275 eq12
    | (have j0 := eq12 (τ X1) (τ X0)
       have j1 := eq275 X0 X1
       grind)
    | (have r₁ := eq12 (τ X1) (τ X0)
       have r₂ := eq275 X0 X1
       grind)
    | exact resolve eq12 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq683 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq679 X0 X1
       have j1 := eq12 (τ X1) (τ X0)
       grind)
    | (have r₁ := eq679 X0 X1
       have r₂ := eq12 (τ X1) (τ X0)
       grind)
    | exact resolve eq679 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq691 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq683
    | (have j0 := eq683 X0 X1
       grind)
    | exact resolve eq683 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq683
  have eq698 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq682 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq682
    | (have j0 := eq682 (σ X0) (σ X1)
       grind)
    | exact resolve eq682 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq708 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq698 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq698
    | (have j0 := eq698 X0 X1
       grind)
    | exact resolve eq698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq711 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq708
    | (have j0 := eq708 X0 X1
       grind)
    | exact resolve eq708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq713 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq711 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq711
    | (have j0 := eq711 X0 X1
       grind)
    | exact resolve eq711 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq715 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq713 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq713
    | (have j0 := eq713 X0 X1
       grind)
    | exact resolve eq713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq722 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq715 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq715
    | (have j0 := eq715 (σ X0) (σ X1)
       grind)
    | exact resolve eq715 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq780 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (k (σ X1) (σ X0))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq691 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq691
    | (have j0 := eq691 (σ X0) (σ X1)
       grind)
    | exact resolve eq691 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq795 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (k (σ X1) (σ X0))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq780 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq780
    | (have j0 := eq780 X0 X1
       grind)
    | exact resolve eq780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq799 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (k (σ X1) (σ X0))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq795
    | (have j0 := eq795 X0 X1
       grind)
    | exact resolve eq795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq801 : ∀ X0 X1 : G, (τ (k (σ X1) (σ X0))) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq799 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq799
    | (have j0 := eq799 X0 X1
       grind)
    | exact resolve eq799 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq802 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (k (σ X1) (σ X0))) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq801 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq801
    | (have j0 := eq801 X0 X1
       grind)
    | exact resolve eq801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq803 : ∀ X0 X1 : G, (M.op X1 X0) = (k (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq802 X0 X1
       have i₂ := eq22 (σ X1) X0
       grind)
    | exact superpose eq22 eq802
    | (have j0 := eq802 X0 X1
       grind)
    | exact resolve eq802 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq802
  have eq804 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq803 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq803
    | (have j0 := eq803 X0 X1
       grind)
    | exact resolve eq803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq809 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq804 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq804
    | (have j0 := eq804 (σ X0) (σ X1)
       grind)
    | exact resolve eq804 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq820 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq809 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq809
    | (have j0 := eq809 X0 X1
       grind)
    | exact resolve eq809 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq4787 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq414 x y
       grind)
    | exact superpose eq414 eq16
    | (have j1 := eq414 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq414 x y
       grind)
    | exact resolve eq16 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq4805 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4787
  have eq4948 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4805
       grind)
    | exact superpose eq4805 eq16
    | exact resolve eq16 eq4805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4950 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq4805
       grind)
    | exact superpose eq4805 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq4805
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq4805
       grind)
    | exact resolve eq12 eq4805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4951 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq4805
       grind)
    | exact superpose eq4805 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4805
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq4805
       grind)
    | exact resolve eq13 eq4805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4953 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62 (σ x) (σ y)
       have i₂ := eq4805
       grind)
    | exact superpose eq4805 eq62
    | exact resolve eq62 eq4805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4961 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4951
  have eq4962 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4950
  have eq4965 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4961
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4961
    | exact resolve eq4961 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4961
  have eq4966 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4962
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4962
    | exact resolve eq4962 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4962
  have eq4968 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq273 eq4965
    | (have j1 := eq273 (σ y) (σ x)
       grind)
    | exact resolve eq4965 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4965
  have eq4971 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq4953
       grind)
    | exact superpose eq4953 eq12
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq4953
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq4953
       grind)
    | exact resolve eq12 eq4953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4953
  have eq4981 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4971
  have eq4987 : (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4981
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq4981
    | exact resolve eq4981 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4981
  have eq5004 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq4987
       grind)
    | exact superpose eq4987 eq10
    | exact resolve eq10 eq4987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4987
  have eq5133 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5004
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5004
    | exact resolve eq5004 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5004
  have eq5146 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq804 x x
       have i₂ := eq5133
       grind)
    | exact superpose eq5133 eq804
    | (have r₁ := eq804 x x
       have r₂ := eq5133
       grind)
    | exact resolve eq804 eq5133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804 eq5133
  have eq5152 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq5146
  have eq5169 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq62 x y
       have i₂ := eq5152
       grind)
    | exact superpose eq5152 eq62
    | exact resolve eq62 eq5152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq5152
  have eq5178 : x = (M.op x x) := by grind
  clear eq5169
  have eq5186 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq5178
       grind)
    | exact superpose eq5178 eq12
    | (have r₁ := eq12 x x
       have r₂ := eq5178
       grind)
    | exact resolve eq12 eq5178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5196 : x = (k x x) := by grind
  clear eq5186
  have eq5223 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq820 x x
       have i₂ := eq5196
       grind)
    | exact superpose eq5196 eq820
    | exact resolve eq820 eq5196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5196
  have eq5227 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5223
  have eq6069 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq820 y x
       have i₂ := eq4966
       grind)
    | exact superpose eq4966 eq820
    | (have j0 := eq820 y x
       grind)
    | exact resolve eq820 eq4966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq4966
  have eq6139 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4805 eq6069
    | exact resolve eq6069 eq4805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4805 eq6069
  have eq6140 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq273 eq6139
    | (have j1 := eq273 x y
       grind)
    | (have r₁ := eq6139
       have r₂ := eq273 (σ y) (σ x)
       grind)
    | exact resolve eq6139 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq6139
  have eq6141 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6140
       have r₂ := eq4948
       grind)
    | exact resolve eq6140 eq4948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6140
  have eq134599 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4968
       have r₂ := eq6141
       grind)
    | exact resolve eq4968 eq6141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4968 eq6141
  have eq134600 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq134599
       have i₂ := eq5227
       grind)
    | exact superpose eq5227 eq134599
    | exact resolve eq134599 eq5227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5227 eq134599
  have eq134601 : x = (M.op x y) := by
    first
    | (have r₁ := eq134600
       have r₂ := eq4948
       grind)
    | exact resolve eq134600 eq4948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4948 eq134600
  have eq134602 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134601
       grind)
    | exact superpose eq134601 eq16
    | exact resolve eq16 eq134601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134631 : x ≠ x ∨ y = (M.op y x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq134601
       grind)
    | exact superpose eq134601 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq134601
       grind)
    | exact resolve eq13 eq134601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134652 : y = (M.op y x) ∨ (k x y) = (M.op x x) := by grind
  clear eq134631
  have eq134676 : y = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq134652
       have i₂ := eq5178
       grind)
    | exact superpose eq5178 eq134652
    | exact resolve eq134652 eq5178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5178 eq134652
  have eq134944 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq134676
       grind)
    | exact superpose eq134676 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq134676
       grind)
    | exact resolve eq12 eq134676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134676
  have eq134967 : (M.op x y) = (k x y) ∨ x = (k x y) := by grind
  clear eq134944
  have eq134968 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq134967
       have i₂ := eq134601
       grind)
    | exact superpose eq134601 eq134967
    | exact resolve eq134967 eq134601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134601 eq134967
  have eq134969 : x = (k x y) := by grind
  clear eq134968
  have eq135008 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq722 x y
       have i₂ := eq134969
       grind)
    | exact superpose eq134969 eq722
    | (have j0 := eq722 x y
       grind)
    | exact resolve eq722 eq134969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq134969
  have eq135087 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq135008
  have eq135106 : False := by grind
  exact eq135106

/-- `Equation3071`: `x = (((x ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_y_pxy_Equation3071 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3071 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3071.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq63 : x ≠ (M.op x y) ∨ (M.op y x) = (k y x) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
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
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) X2) ≠ X0 ∨ (M.op X0 (M.op (M.op (M.op X0 X1) X0) X2)) = X0 ∨ (k (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X0 X1) X0) X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op (M.op X0 X1) X0) X2) X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq93
    | (have j0 := eq93 (σ X0) (σ X1)
       grind)
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq93 y x
       grind)
    | exact superpose eq93 eq72
    | (have j1 := eq93 y x
       grind)
    | exact resolve eq72 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq93 x y
       grind)
    | exact superpose eq93 eq44
    | (have j1 := eq93 x y
       grind)
    | exact resolve eq44 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq119 eq93
    | (have j0 := eq93 (σ x) (σ y)
       grind)
    | exact resolve eq93 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq122
    | exact resolve eq122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq126 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq123
       have r₂ := eq27
       grind)
    | exact resolve eq123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq126
    | exact resolve eq126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq174 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq140 eq16
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq219 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ x)) X0) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq128 eq51
    | exact resolve eq51 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq231 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f231_14 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ x)) X0) (σ x)) ∨ x = (M.op x y) := by
      intro X0
      grind
    have f231_20 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
      intro X0 X1 X2
      grind
    have f231_23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
    have f231_24 : x ≠ (M.op x y) := by grind
    have f231_26 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ x)) X0) (σ x)) := by
      intro X0
      first
      | (have j0 := f231_14 X0
         grind)
      | (have r₁ := f231_14 X0
         have r₂ := f231_24
         grind)
      | exact resolve f231_14 f231_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f231_63 : (σ x) = (M.op (σ x) (σ x)) := by
      first
      | (have i₁ := f231_20 (σ x) (σ x) (σ x)
         have i₂ := f231_26 (σ x)
         grind)
      | exact superpose f231_26 f231_20
      | exact resolve f231_20 f231_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f231_67 : False := by
      first
      | (have r₁ := f231_63
         have r₂ := f231_23
         grind)
      | exact resolve f231_63 f231_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f231_67
  have eq250 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq231 eq226
    | exact resolve eq226 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq252 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq231 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq231
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq231
       grind)
    | exact resolve eq13 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq254 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq252
  have eq255 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq250 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq257 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq254 eq49
    | exact resolve eq49 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq254
  have eq261 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq257
    | exact resolve eq257 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq264 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93 x x
       have i₂ := eq261
       grind)
    | exact superpose eq261 eq93
    | (have j0 := eq93 x x
       grind)
    | exact resolve eq93 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq265 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq264
  have eq284 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq293 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq265
       grind)
    | exact superpose eq265 eq14
    | exact resolve eq14 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq255
    | (have j0 := eq255 (σ y)
       grind)
    | exact resolve eq255 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq327 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq38
  have eq381 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq64
    | (have r₁ := eq64
       have r₂ := eq128
       grind)
    | exact resolve eq64 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq382 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq381
  have eq404 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq293 X0
       have i₂ := eq265
       grind)
    | exact superpose eq265 eq293
    | exact resolve eq293 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq293
  have eq411 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq404 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq412 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq411 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq411
    | (have j0 := eq411 y
       grind)
    | exact resolve eq411 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq427 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq76
    | (have r₁ := eq76
       have r₂ := eq128
       grind)
    | exact resolve eq76 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq128
  have eq428 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq427
  have eq479 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq482 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq479 X0 X1
       have j1 := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq479 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | exact resolve eq479 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq486 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq482 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq482
    | (have j0 := eq482 X0 X1
       grind)
    | exact resolve eq482 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq490 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq428 eq119
    | exact resolve eq119 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq493 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq490
  have eq503 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq493 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq493
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq493
       grind)
    | exact resolve eq13 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq505 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq503
  have eq508 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq505
    | exact resolve eq505 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq508 eq119
    | exact resolve eq119 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq522 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq519
  have eq526 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq522
       have r₂ := eq27
       grind)
    | exact resolve eq522 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq529 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq526 eq29
    | exact resolve eq29 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq536 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq526 eq119
    | exact resolve eq119 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq544 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq536
  have eq552 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq529
    | exact resolve eq529 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq629 : x = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq552 eq412
    | exact resolve eq412 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq631 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq708 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq544 eq61
    | exact resolve eq61 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq544
  have eq710 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq708
    | exact resolve eq708 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq747 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq50 eq77
    | exact resolve eq77 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq77
  have eq756 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq747
       have r₂ := eq710
       grind)
    | exact resolve eq747 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq747
  have eq804 : y = (k x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq552 eq756
    | exact resolve eq756 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq756
  have eq809 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq804
       have r₂ := eq75
       grind)
    | exact resolve eq804 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq804
  have eq955 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq809
       grind)
    | exact superpose eq809 eq44
    | exact resolve eq44 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq958 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq955
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq955
    | exact resolve eq955 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq994 : ∀ X0 : G, (k (τ X0) (k y x)) = (τ (k X0 (k (σ y) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq284 X0 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq284
    | exact resolve eq284 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq1021 : ∀ X0 : G, (k (k y x) (τ X0)) = (τ (k (k (σ y) (σ x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq327 (k y x) X0
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq327
    | exact resolve eq327 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq1116 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq958 eq93
    | (have j0 := eq93 (σ x) (σ y)
       grind)
    | exact resolve eq93 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1117 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq1116
    | exact resolve eq1116 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1120 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1117
    | exact resolve eq1117 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1355 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1120
       grind)
    | exact superpose eq1120 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1120
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1120
       grind)
    | exact resolve eq13 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1361 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1355
  have eq1363 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1361
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1361
    | exact resolve eq1361 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361
  have eq1406 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq629
       have r₂ := eq631
       grind)
    | exact resolve eq629 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq1568 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1363
       grind)
    | exact superpose eq1363 eq44
    | exact resolve eq44 eq1363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1363
  have eq1570 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1568
    | exact resolve eq1568 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568
  have eq1635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1570 eq93
    | (have j0 := eq93 (σ x) (σ y)
       grind)
    | exact resolve eq93 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570
  have eq1636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1635
    | exact resolve eq1635 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq1639 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1636
       have r₂ := eq27
       grind)
    | exact resolve eq1636 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq1641 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1639
    | exact resolve eq1639 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639
  have eq1642 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1641
  have eq28183 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq1406
       grind)
    | exact superpose eq1406 eq104
    | exact resolve eq104 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq1406
  have eq28240 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq28183
       have r₂ := eq631
       grind)
    | exact resolve eq28183 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq28183
  have eq28241 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28240
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28240
    | exact resolve eq28240 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28240
  have eq28251 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28241 eq382
    | exact resolve eq382 eq28241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq28241
  have eq28290 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq28251
  have eq28442 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28290 eq14
    | exact resolve eq14 eq28290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28290
  have eq28480 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq28442
    | (have j0 := eq28442 X0
       grind)
    | exact resolve eq28442 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28442
  have eq29713 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq295 eq28480
    | exact resolve eq28480 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq28480
  have eq29751 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq29713
  have eq29758 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq29751
    | exact resolve eq29751 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29751
  have eq29973 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29758 eq27
    | exact resolve eq27 eq29758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29758
  have eq30010 : x = (M.op x y) := by
    first
    | (have r₁ := eq29973
       have r₂ := eq526
       grind)
    | exact resolve eq29973 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq29973
  have eq30012 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq30010 eq20
    | exact resolve eq20 eq30010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq30016 : x ≠ x ∨ (M.op y x) = (k y x) := by
    first
    | exact superpose eq30010 eq63
    | (have r₁ := eq63
       have r₂ := eq30010
       grind)
    | exact resolve eq63 eq30010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq30062 : x = (M.op x x) := by
    first
    | exact superpose eq30010 eq219
    | exact resolve eq219 eq30010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq30081 : (M.op y x) = (k y x) := by grind
  clear eq30016
  have eq30132 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30012
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30012
    | exact resolve eq30012 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30012
  have eq30135 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30132 eq26
    | exact resolve eq26 eq30132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq30444 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq30062
       grind)
    | exact superpose eq30062 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq30062
       grind)
    | exact resolve eq13 eq30062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30062
  have eq30462 : x = (k x x) := by grind
  clear eq30444
  have eq30570 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq486 x x
       have i₂ := eq30462
       grind)
    | exact superpose eq30462 eq486
    | exact resolve eq486 eq30462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq30574 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq30570
  have eq30582 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq30574
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30574
    | exact resolve eq30574 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30574
  have eq30597 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30132 eq30582
    | exact resolve eq30582 eq30132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30582
  have eq30632 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq30597 eq14
    | exact resolve eq14 eq30597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30662 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq30597 eq30632
    | exact resolve eq30632 eq30597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30632
  have eq31114 : (k (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq30081
       grind)
    | exact superpose eq30081 eq72
    | exact resolve eq72 eq30081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq31146 : (k (σ y) (σ (M.op x y))) = (σ (M.op y x)) := by
    first
    | exact superpose eq30132 eq31114
    | exact resolve eq31114 eq30132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31114
  have eq31349 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30135 eq30662
    | exact resolve eq30662 eq30135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30662
  have eq31493 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1642 eq31349
    | exact resolve eq31349 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642
  have eq31526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq30132 eq31493
    | exact resolve eq31493 eq30132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31493
  have eq31537 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq31526
       have r₂ := eq27
       grind)
    | exact resolve eq31526 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31526
  have eq31563 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ (M.op x y)) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq31537 eq14
    | exact resolve eq14 eq31537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31592 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq30135 eq31563
    | exact resolve eq31563 eq30135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31563
  have eq31957 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq31349 eq31592
    | exact resolve eq31592 eq31349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31349 eq31592
  have eq32011 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30135 eq31957
    | exact resolve eq31957 eq30135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30135 eq31957
  have eq32040 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq32011 eq27
    | exact resolve eq27 eq32011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32011
  have eq32255 : ∀ X0 : G, (k (τ X0) (k y x)) = (τ (k X0 (k (σ y) (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq30132 eq994
    | exact resolve eq994 eq30132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq32256 : ∀ X0 : G, (τ (k X0 (k (σ y) (σ (M.op x y))))) = (k (τ X0) (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq32255 X0
       have i₂ := eq30081
       grind)
    | exact superpose eq30081 eq32255
    | exact resolve eq32255 eq30081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32255
  have eq32313 : (τ (k (σ x) (k (σ y) (σ (M.op x y))))) = (k x (M.op y x)) := by
    first
    | exact superpose eq28 eq32256
    | exact resolve eq32256 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32256
  have eq32353 : (τ (k (σ (M.op x y)) (k (σ y) (σ (M.op x y))))) = (k x (M.op y x)) := by
    first
    | exact superpose eq30132 eq32313
    | exact resolve eq32313 eq30132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32313
  have eq33073 : ∀ X0 : G, (k (k y x) (τ X0)) = (τ (k (k (σ y) (σ (M.op x y))) X0)) := by
    intro X0
    first
    | exact superpose eq30132 eq1021
    | exact resolve eq1021 eq30132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq33074 : ∀ X0 : G, (τ (k (k (σ y) (σ (M.op x y))) X0)) = (k (M.op y x) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33073 X0
       have i₂ := eq30081
       grind)
    | exact superpose eq30081 eq33073
    | exact resolve eq33073 eq30081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30081 eq33073
  have eq33133 : (τ (k (k (σ y) (σ (M.op x y))) (σ x))) = (k (M.op y x) x) := by
    first
    | exact superpose eq28 eq33074
    | exact resolve eq33074 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq33074
  have eq33171 : (τ (k (k (σ y) (σ (M.op x y))) (σ (M.op x y)))) = (k (M.op y x) x) := by
    first
    | exact superpose eq30132 eq33133
    | exact resolve eq33133 eq30132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33133
  have eq38706 : (k x (M.op y x)) = (τ (k (σ (M.op x y)) (M.op (σ y) (σ (M.op x y))))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq32353
       have i₂ := eq93 sF3 sF1
       grind)
    | exact superpose eq93 eq32353
    | (have j1 := eq93 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq32353 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32353
  have eq38756 : (τ (k (σ (M.op x y)) (σ (M.op x y)))) = (k x (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq31537 eq38706
    | exact resolve eq38706 eq31537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38706
  have eq38759 : (k (M.op x y) (M.op x y)) = (k x (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq174 eq38756
    | exact resolve eq38756 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq38756
  have eq38760 : (k x x) = (k x (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq30010 eq38759
    | exact resolve eq38759 eq30010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38759
  have eq38761 : x = (k x (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq38760
       have i₂ := eq30462
       grind)
    | exact superpose eq30462 eq38760
    | exact resolve eq38760 eq30462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30462 eq38760
  have eq38762 : (σ (M.op x y)) = (σ y) ∨ x = (k x (M.op y x)) := by
    first
    | exact superpose eq31537 eq38761
    | exact resolve eq38761 eq31537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38761
  have eq38763 : x = (k x (M.op y x)) := by
    first
    | (have r₁ := eq38762
       have r₂ := eq32040
       grind)
    | exact resolve eq38762 eq32040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38762
  have eq38768 : x = (M.op x (M.op y x)) ∨ x = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq93 x (M.op y x)
       have i₂ := eq38763
       grind)
    | exact superpose eq38763 eq93
    | (have j0 := eq93 x (M.op y x)
       grind)
    | exact resolve eq93 eq38763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38771 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op y x))) := by
    first
    | (have i₁ := eq481 x (M.op y x)
       have i₂ := eq38763
       grind)
    | exact superpose eq38763 eq481
    | (have j0 := eq481 x (M.op y x)
       grind)
    | exact resolve eq481 eq38763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481 eq38763
  have eq38779 : (σ x) = (M.op (σ x) (σ (M.op y x))) := by grind
  clear eq38771
  have eq38780 : x = (M.op x (M.op y x)) := by grind
  clear eq38768
  have eq38787 : (σ x) = (M.op (σ x) (k (σ y) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq38779
       have i₂ := eq31146
       grind)
    | exact superpose eq31146 eq38779
    | exact resolve eq38779 eq31146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31146 eq38779
  have eq38796 : (σ x) = (M.op (σ x) (k (σ y) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq38787
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38787
    | exact resolve eq38787 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38787
  have eq38805 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq30132 eq38796
    | exact resolve eq38796 eq30132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38796
  have eq38831 : x ≠ x ∨ (k (M.op y x) x) = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq13 (M.op y x) x
       have i₂ := eq38780
       grind)
    | exact superpose eq38780 eq13
    | (have j0 := eq13 (M.op y x) x
       grind)
    | (have r₁ := eq13 (M.op y x) x
       have r₂ := eq38780
       grind)
    | exact resolve eq13 eq38780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38849 : (k (M.op y x) x) = (M.op (M.op y x) x) := by grind
  clear eq38831
  have eq38907 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (k (σ y) (σ (M.op x y))) (σ (M.op x y))) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq38805 eq13
    | (have j0 := eq13 (k (σ y) (σ (M.op x y))) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (k (σ y) (σ (M.op x y))) (σ (M.op x y))
       have r₂ := eq38805
       grind)
    | exact resolve eq13 eq38805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38805
  have eq38925 : (k (k (σ y) (σ (M.op x y))) (σ (M.op x y))) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) := by grind
  clear eq38907
  have eq42271 : (τ (k (k (σ y) (σ (M.op x y))) (σ (M.op x y)))) = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq33171
       have i₂ := eq38849
       grind)
    | exact superpose eq38849 eq33171
    | exact resolve eq33171 eq38849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33171 eq38849
  have eq42272 : (M.op (M.op y x) x) = (τ (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | exact superpose eq38925 eq42271
    | exact resolve eq42271 eq38925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38925 eq42271
  have eq42448 : (M.op (M.op y x) x) = (τ (M.op (M.op (σ y) (σ (M.op x y))) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq42272
       have i₂ := eq93 sF3 sF1
       grind)
    | exact superpose eq93 eq42272
    | (have j1 := eq93 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq42272 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq42272
  have eq42496 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op y x) x) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq31537 eq42448
    | exact resolve eq42448 eq31537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42448
  have eq42499 : (τ (σ (M.op x y))) = (M.op (M.op y x) x) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq30597 eq42496
    | exact resolve eq42496 eq30597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30597 eq42496
  have eq42500 : (M.op x y) = (M.op (M.op y x) x) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq30 eq42499
    | exact resolve eq42499 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq42499
  have eq42501 : x = (M.op (M.op y x) x) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq30010 eq42500
    | exact resolve eq42500 eq30010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42500
  have eq42502 : (σ (M.op x y)) = (σ y) ∨ x = (M.op (M.op y x) x) := by
    first
    | exact superpose eq31537 eq42501
    | exact resolve eq42501 eq31537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31537 eq42501
  have eq42503 : x = (M.op (M.op y x) x) := by
    first
    | (have r₁ := eq42502
       have r₂ := eq32040
       grind)
    | exact resolve eq42502 eq32040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42502
  have eq42509 : ∀ X0 : G, (M.op y x) = (M.op (M.op (M.op x (M.op y x)) X0) (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op y x) x X0
       have i₂ := eq42503
       grind)
    | exact superpose eq42503 eq14
    | exact resolve eq14 eq42503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42503
  have eq42536 : ∀ X0 : G, (M.op y x) = (M.op (M.op x X0) (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq42509 X0
       have i₂ := eq38780
       grind)
    | exact superpose eq38780 eq42509
    | exact resolve eq42509 eq38780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42509
  have eq42882 : (M.op y x) = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq42536 (M.op y x)
       have i₂ := eq38780
       grind)
    | exact superpose eq38780 eq42536
    | exact resolve eq42536 eq38780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42536
  have eq42937 : x = (M.op y x) := by
    first
    | (have i₁ := eq42882
       have i₂ := eq38780
       grind)
    | exact superpose eq38780 eq42882
    | exact resolve eq42882 eq38780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42882
  have eq42988 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq42937
       grind)
    | exact superpose eq42937 eq14
    | exact resolve eq14 eq42937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42937
  have eq43016 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq42988 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42988
    | (have j0 := eq42988 X0
       grind)
    | exact resolve eq42988 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42988
  have eq43037 : ∀ X0 : G, y = (M.op (M.op x X0) y) := by
    intro X0
    first
    | exact superpose eq30010 eq43016
    | exact resolve eq43016 eq30010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43016
  have eq43489 : y = (M.op x y) := by
    first
    | (have i₁ := eq43037 (M.op y x)
       have i₂ := eq38780
       grind)
    | exact superpose eq38780 eq43037
    | exact resolve eq43037 eq38780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38780 eq43037
  have eq43542 : y = (M.op x y) := by
    first
    | (have i₁ := eq43489
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq43489
    | exact resolve eq43489 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq43489
  have eq43559 : x = y := by
    first
    | exact superpose eq30010 eq43542
    | exact resolve eq43542 eq30010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30010 eq43542
  have eq43581 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq43559
       grind)
    | exact superpose eq43559 eq24
    | exact resolve eq24 eq43559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq43559
  have eq43783 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq43581
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43581
    | exact resolve eq43581 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq43581
  have eq43844 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30132 eq43783
    | exact resolve eq43783 eq30132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30132 eq43783
  have eq43896 : False := by grind
  exact eq43896

/-- `Equation3071`: `x = (((x ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation3071 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3071 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3071.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq29
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq36
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq36 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1009 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq127 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq127
    | (have j0 := eq127 (σ X0) (σ X1)
       grind)
    | exact resolve eq127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq4875 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq77 X0 (σ X0)
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4896 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq4897 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4896 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4896
  have eq4899 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4875 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4875
  have eq4900 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4899 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4899
  have eq4902 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4897 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4897
    | (have j0 := eq4897 X0
       grind)
    | exact resolve eq4897 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4897
  have eq4950 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq4902 X0
       grind)
    | exact superpose eq4902 eq43
    | (have j1 := eq4902 X0
       grind)
    | exact resolve eq43 eq4902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq4902
  have eq4966 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4950 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4950
    | (have j0 := eq4950 X0
       grind)
    | exact resolve eq4950 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4950
  have eq4967 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4966 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4966
  have eq4969 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4967 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4967
    | exact resolve eq4967 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4996 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4967 X0
       grind)
    | exact superpose eq4967 eq11
    | exact resolve eq11 eq4967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4967
  have eq5059 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4969 X0
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq4969
    | exact resolve eq4969 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4969
  have eq5303 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq5059 X0
       grind)
    | exact superpose eq5059 eq11
    | exact resolve eq11 eq5059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5059
  have eq5412 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5303 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq5303
    | exact resolve eq5303 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5303
  have eq6136 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq6163 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq6136 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq6136
    | exact resolve eq6136 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6136
  have eq6197 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6163 X0
       have i₂ := eq5412 X0
       grind)
    | exact superpose eq5412 eq6163
    | exact resolve eq6163 eq5412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6163
  have eq6215 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq6197
  have eq29458 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1009 (τ X0) (τ X1)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq1009
    | (have j0 := eq1009 (τ X0) (τ X1)
       grind)
    | exact resolve eq1009 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq29538 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X0))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29458 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq29458
    | (have j0 := eq29458 X0 X1
       grind)
    | exact resolve eq29458 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29458
  have eq29594 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29538 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29538
    | (have j0 := eq29538 X0 X1
       grind)
    | exact resolve eq29538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29538
  have eq29649 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29594 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq29594
    | (have j0 := eq29594 X0 X1
       grind)
    | exact resolve eq29594 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29594
  have eq29701 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29649 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29649
    | (have j0 := eq29649 X0 X1
       grind)
    | exact resolve eq29649 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29649
  have eq29745 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29701 X0 X1
       have i₂ := eq4996 (σ (τ X1))
       grind)
    | exact superpose eq4996 eq29701
    | (have j0 := eq29701 X0 X1
       grind)
    | exact resolve eq29701 eq4996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29701
  have eq29787 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29745 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq29745
    | (have j0 := eq29745 X0 X1
       grind)
    | exact resolve eq29745 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29745
  have eq29825 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29787 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq29787
    | (have j0 := eq29787 X0 X1
       grind)
    | exact resolve eq29787 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq29787
  have eq29860 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29825 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq29825
    | (have j0 := eq29825 X0 X1
       grind)
    | exact resolve eq29825 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29825
  have eq29887 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29860 X0 X1
       have i₂ := eq5412 X1
       grind)
    | exact superpose eq5412 eq29860
    | (have j0 := eq29860 X0 X1
       grind)
    | exact resolve eq29860 eq5412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29860
  have eq29910 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29887 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29887
    | (have j0 := eq29887 X0 X1
       grind)
    | exact resolve eq29887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29887
  have eq48344 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq4900 X0 X1
       grind)
    | exact superpose eq4900 eq36
    | (have j1 := eq4900 X0 X1
       grind)
    | exact resolve eq36 eq4900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq4900
  have eq48567 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48344 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48344
    | (have j0 := eq48344 X0 X1
       grind)
    | exact resolve eq48344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48344
  have eq50843 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48567 (τ X1) X0
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq48567
    | (have j0 := eq48567 (τ X0) X1
       grind)
    | exact resolve eq48567 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq48567
  have eq51114 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50843 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50843
    | (have j0 := eq50843 X0 X1
       grind)
    | exact resolve eq50843 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50843
  have eq51212 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51114 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51114
    | (have j0 := eq51114 X0 X1
       grind)
    | exact resolve eq51114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51114
  have eq52297 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq51212 X0 X1
       grind)
    | exact superpose eq51212 eq11
    | (have j1 := eq51212 X0 X1
       grind)
    | exact resolve eq11 eq51212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52420 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq51212 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51212
  have eq52515 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52297 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq52297
    | (have j0 := eq52297 X0 X1
       grind)
    | exact resolve eq52297 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52297
  have eq53930 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52515 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq52515
    | (have j0 := eq52515 (σ X0) (σ X1)
       grind)
    | exact resolve eq52515 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52515
  have eq54252 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53930 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq53930
    | (have j0 := eq53930 X0 X1
       grind)
    | exact resolve eq53930 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53930
  have eq54302 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54252 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54252
    | (have j0 := eq54252 X0 X1
       grind)
    | exact resolve eq54252 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54252
  have eq54337 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54302 X0 X1
       have i₂ := eq4996 X1
       grind)
    | exact superpose eq4996 eq54302
    | (have j0 := eq54302 X0 X1
       grind)
    | exact resolve eq54302 eq4996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4996 eq54302
  have eq54368 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54337 X0 X1
       have i₂ := eq5412 X1
       grind)
    | exact superpose eq5412 eq54337
    | (have j0 := eq54337 X0 X1
       grind)
    | exact resolve eq54337 eq5412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5412 eq54337
  have eq62964 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54368 x y
       grind)
    | exact superpose eq54368 eq16
    | (have j1 := eq54368 x y
       grind)
    | exact resolve eq16 eq54368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54368
  have eq64187 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq62964
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq62964
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq62964 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62964
  have eq64193 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq64187
  have eq64194 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq64193
  have eq64880 : (τ x) ≠ (τ x) ∨ x = (M.op y y) ∨ (τ (k x y)) = (τ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq52420 x y
       have i₂ := eq64194
       grind)
    | exact superpose eq64194 eq52420
    | (have j0 := eq52420 x y
       grind)
    | exact resolve eq52420 eq64194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52420
  have eq64881 : (τ x) ≠ (τ x) ∨ x = (M.op y y) ∨ (τ (k x y)) = (τ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq64880
  have eq64882 : x = (M.op y y) ∨ (τ (k x y)) = (τ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq64881
  have eq95089 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (k x y)) = (τ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq6215 y
       have i₂ := eq64882
       grind)
    | exact superpose eq64882 eq6215
    | exact resolve eq6215 eq64882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64882
  have eq95146 : (τ (k x y)) = (τ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq95089
       have r₂ := eq16
       grind)
    | exact resolve eq95089 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95089
  have eq96022 : (k x y) = (σ (τ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11 (k x y)
       have i₂ := eq95146
       grind)
    | exact superpose eq95146 eq11
    | exact resolve eq11 eq95146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95146
  have eq96261 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq96022
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq96022
    | exact resolve eq96022 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96022
  have eq96406 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq29910 x y
       have i₂ := eq96261
       grind)
    | exact superpose eq96261 eq29910
    | (have j0 := eq29910 x y
       grind)
    | exact resolve eq29910 eq96261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29910 eq96261
  have eq96409 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq96406
  have eq96410 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq96409
  have eq98068 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96410
       grind)
    | exact superpose eq96410 eq16
    | exact resolve eq16 eq96410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96410
  have eq98888 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq98068
       have i₂ := eq64194
       grind)
    | exact superpose eq64194 eq98068
    | exact resolve eq98068 eq64194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64194 eq98068
  have eq98889 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq98888
  have eq98890 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq98889
  have eq98908 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq6215 y
       have i₂ := eq98890
       grind)
    | exact superpose eq98890 eq6215
    | exact resolve eq6215 eq98890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98890
  have eq98966 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq98908
       have r₂ := eq16
       grind)
    | exact resolve eq98908 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98908
  have eq98996 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq98966
       grind)
    | exact superpose eq98966 eq10
    | exact resolve eq10 eq98966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98966
  have eq99210 : x = (M.op y y) := by
    first
    | (have i₁ := eq98996
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq98996
    | exact resolve eq98996 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98996
  have eq99394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6215 y
       have i₂ := eq99210
       grind)
    | exact superpose eq99210 eq6215
    | exact resolve eq6215 eq99210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6215 eq99210
  have eq99453 : False := by grind
  exact eq99453

/-- `Equation3071`: `x = (((x ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_x_pxy_Equation3071 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3071 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3071.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq273 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq276 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq274 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq274 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq274 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq287 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq276 (σ X0)
       grind)
    | exact superpose eq276 eq15
    | exact resolve eq15 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq287 X0
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq287
    | exact resolve eq287 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq287
  have eq350 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq62 (σ X0) (σ X0)
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq62
    | exact resolve eq62 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq352 X0 X1
       have j1 := eq353 X0 X1
       grind)
    | (have r₁ := eq352 X0 X1
       have r₂ := eq353 X0 X1
       grind)
    | exact resolve eq352 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq502 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq354 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq354
    | exact resolve eq354 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq354 X1 (σ X0)
       grind)
    | exact superpose eq354 eq15
    | (have j1 := eq354 X1 (σ X0)
       grind)
    | exact resolve eq15 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq553 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq502 X1 (τ X0)
       grind)
    | exact superpose eq502 eq17
    | (have j1 := eq502 X1 (τ X0)
       grind)
    | exact resolve eq17 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq502
  have eq690 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq553 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq553
    | exact resolve eq553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq751 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq690 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq690
    | (have j0 := eq690 X0 X1
       grind)
    | exact resolve eq690 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq1812 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq513 x y
       grind)
    | exact superpose eq513 eq16
    | (have j1 := eq513 x y
       grind)
    | exact resolve eq16 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq1883 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1812
       have i₂ := eq751 x y
       grind)
    | exact superpose eq751 eq1812
    | (have j1 := eq751 (σ x) (σ y)
       grind)
    | (have r₁ := eq1812
       have r₂ := eq751 x y
       grind)
    | exact resolve eq1812 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751 eq1812
  have eq1884 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1883
  have eq1892 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq62 y x
       have i₂ := eq1884
       grind)
    | exact superpose eq1884 eq62
    | exact resolve eq62 eq1884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884
  have eq1900 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq62 (σ y) (σ x)
       have i₂ := eq1892
       grind)
    | exact superpose eq1892 eq62
    | exact resolve eq62 eq1892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1892
  have eq1904 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1900
       have i₂ := eq306 y
       grind)
    | exact superpose eq306 eq1900
    | exact resolve eq1900 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900
  have eq1947 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq350 y
       have i₂ := eq1904
       grind)
    | exact superpose eq1904 eq350
    | exact resolve eq350 eq1904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq1949 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq353 y X0
       have i₂ := eq1904
       grind)
    | exact superpose eq1904 eq353
    | (have j0 := eq353 y X0
       grind)
    | (have r₁ := eq353 y x
       have r₂ := eq1904
       grind)
    | exact resolve eq353 eq1904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904
  have eq1958 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq1949 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949
  have eq1964 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1958 X0
       have j1 := eq353 y X0
       grind)
    | (have r₁ := eq1958 X0
       have r₂ := eq353 y x
       grind)
    | exact resolve eq1958 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq1958
  have eq1966 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1947
       have i₂ := eq306 y
       grind)
    | exact superpose eq306 eq1947
    | exact resolve eq1947 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq1947
  have eq1967 : (σ y) = (σ (M.op y y)) := by grind
  clear eq1966
  have eq1974 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1967
       grind)
    | exact superpose eq1967 eq10
    | exact resolve eq10 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967
  have eq2018 : y = (M.op y y) := by
    first
    | (have i₁ := eq1974
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1974
    | exact resolve eq1974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974
  have eq2026 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq2018
       grind)
    | exact superpose eq2018 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq2018
       grind)
    | exact resolve eq12 eq2018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018
  have eq2040 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq2026 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2026
  have eq2113 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq1964 (σ X0)
       grind)
    | exact superpose eq1964 eq15
    | exact resolve eq15 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964
  have eq2133 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2113 X0
       have i₂ := eq2040 X0
       grind)
    | exact superpose eq2040 eq2113
    | exact resolve eq2113 eq2040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040 eq2113
  have eq2225 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2133 x
       grind)
    | exact superpose eq2133 eq16
    | (have r₁ := eq16
       have r₂ := eq2133 x
       grind)
    | exact resolve eq16 eq2133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq2259 : False := by grind
  exact eq2259

/-- `Equation3071`: `x = (((x ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation3071 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3071 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3071.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq43 X0 X1
       grind)
    | exact resolve eq13 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq84 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq171 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq175 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq43
    | (have j1 := eq83 X0 X1
       grind)
    | exact resolve eq43 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq177 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq698 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq734 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq801 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (σ X0) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 (M.op X0 X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq177
    | (have j0 := eq177 X0 (M.op X0 X1)
       have j1 := eq55 X0 X1
       grind)
    | exact resolve eq177 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq812 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (σ X0) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq801 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq983 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq171
       have i₂ := eq734 x y
       grind)
    | exact superpose eq734 eq171
    | (have j1 := eq734 (σ x) (σ y)
       grind)
    | (have r₁ := eq171
       have r₂ := eq734 x y
       grind)
    | (have r₁ := eq171
       have r₂ := eq734 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq171
       have r₂ := eq734 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq171 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq734
  have eq984 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq983
  have eq1123 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (τ X1) (τ X0)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq175
    | (have j0 := eq175 (τ X0) (τ X1)
       grind)
    | exact resolve eq175 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq175
  have eq1146 : ∀ X0 X1 : G, (k X0 X1) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1123 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1123
    | (have j0 := eq1123 X0 X1
       grind)
    | exact resolve eq1123 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1151 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1146 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1146
    | (have j0 := eq1146 X0 X1
       grind)
    | exact resolve eq1146 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1154 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1151 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1151
    | (have j0 := eq1151 X0 X1
       grind)
    | exact resolve eq1151 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1155 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1154 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1154
    | (have j0 := eq1154 X0 X1
       grind)
    | exact resolve eq1154 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq1156 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1155 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1155
    | (have j0 := eq1155 X0 X1
       grind)
    | exact resolve eq1155 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1157 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1156 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1156
    | (have j0 := eq1156 X0 X1
       grind)
    | exact resolve eq1156 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq22103 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq984
       grind)
    | exact superpose eq984 eq16
    | exact resolve eq16 eq984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq22104 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22103
       have r₂ := eq22 x
       grind)
    | exact resolve eq22103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22103
  have eq22362 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq812 x y
       have i₂ := eq22104
       grind)
    | exact superpose eq22104 eq812
    | exact resolve eq812 eq22104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq22104
  have eq22381 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22362
  have eq22384 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22381
       grind)
    | exact superpose eq22381 eq16
    | exact resolve eq16 eq22381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22381
  have eq22385 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq22384
       have r₂ := eq22 x
       grind)
    | exact resolve eq22384 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22384
  have eq22663 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22385
       grind)
    | exact superpose eq22385 eq16
    | exact resolve eq16 eq22385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22672 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55 (σ x) (σ y)
       have i₂ := eq22385
       grind)
    | exact superpose eq22385 eq55
    | exact resolve eq55 eq22385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq22385
  have eq22717 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq22672
  have eq22742 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq22717
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq22717
    | exact resolve eq22717 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22717
  have eq23047 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22742
       grind)
    | exact superpose eq22742 eq10
    | exact resolve eq10 eq22742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22742
  have eq23153 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq23047
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23047
    | exact resolve eq23047 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23047
  have eq23481 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23153
       grind)
    | exact superpose eq23153 eq16
    | exact resolve eq16 eq23153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23153
  have eq23482 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq23481
       have r₂ := eq22 x
       grind)
    | exact resolve eq23481 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23481
  have eq23495 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq23482
       grind)
    | exact superpose eq23482 eq10
    | exact resolve eq10 eq23482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23482
  have eq23604 : y = (k x y) := by
    first
    | (have i₁ := eq23495
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq23495
    | exact resolve eq23495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23495
  have eq23888 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1157 x y
       have i₂ := eq23604
       grind)
    | exact superpose eq23604 eq1157
    | (have j0 := eq1157 x y
       grind)
    | exact resolve eq1157 eq23604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157 eq23604
  have eq23893 : x = y ∨ y = (M.op x y) := by grind
  clear eq23888
  have eq23901 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23893
       grind)
    | exact superpose eq23893 eq16
    | exact resolve eq16 eq23893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23893
  have eq23906 : y = (M.op x y) := by
    first
    | (have r₁ := eq23901
       have r₂ := eq22 x
       grind)
    | exact resolve eq23901 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23901
  have eq24071 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22663
       have i₂ := eq23906
       grind)
    | exact superpose eq23906 eq22663
    | exact resolve eq22663 eq23906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22663 eq23906
  have eq24107 : (σ x) = (σ y) := by grind
  clear eq24071
  have eq24109 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24107
       grind)
    | exact superpose eq24107 eq10
    | exact resolve eq10 eq24107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24107
  have eq24216 : x = y := by
    first
    | (have i₁ := eq24109
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24109
    | exact resolve eq24109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24109
  have eq24238 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24216
       grind)
    | exact superpose eq24216 eq16
    | exact resolve eq16 eq24216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24216
  have eq24244 : False := by grind
  exact eq24244

/-- `Equation3081`: `x = (((x ◇ y) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_pxy_pyx_Equation3081 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3081 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3081.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) = X0 := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
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
  have eq56 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) y) X0) x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X1) X0 X2
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X1) X1 X0
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq89 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq111 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq215 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq223 : (M.op x y) ≠ (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq215 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq215
       grind)
    | exact resolve eq13 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq224 : x = (k x (M.op x y)) := by grind
  clear eq223
  have eq227 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq224 eq45
    | exact resolve eq45 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq224
  have eq231 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq227
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq227
    | exact resolve eq227 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq234 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq231 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq234
  have eq239 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq247 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq239 eq13
    | (have j0 := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq239
       grind)
    | exact resolve eq13 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq247
  have eq262 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = X0 ∨ (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq12
    | (have j0 := eq12 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq12 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) X2
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq268 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq264 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq269 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq262 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq402 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq59
    | (have j0 := eq59 (σ x) X0 (σ y)
       grind)
    | exact resolve eq59 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op (M.op (M.op X0 X1) X2) X2)
       have i₂ := eq59 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq69 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq860 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq864 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq850 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq867 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq864 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq864 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq864 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq864 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq877 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq867 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq867
    | (have j0 := eq867 X0 X1
       grind)
    | exact resolve eq867 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq1115 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq235 eq12
    | (have j0 := eq12 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ x) (σ (M.op x y))
       have r₂ := eq235
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ x)
       have r₂ := eq235
       grind)
    | exact resolve eq12 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq1126 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1115
  have eq1127 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1126
  have eq1128 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq231 eq1127
    | exact resolve eq1127 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq1127
  have eq1166 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  have eq1290 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 (M.op (M.op X0 X1) X0) X0 X2
       have i₂ := eq418 X0 X1 X0
       grind)
    | exact superpose eq418 eq59
    | exact resolve eq59 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq418
  have eq1739 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) X0)) := by
    intro X0
    first
    | exact superpose eq402 eq268
    | exact resolve eq268 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq1746 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1128 eq1739
    | exact resolve eq1739 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128 eq1739
  have eq15295 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq15296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq15295
    | exact resolve eq15295 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15295
  have eq15307 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq15296
       have r₂ := eq27
       grind)
    | exact resolve eq15296 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15296
  have eq15310 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq15307
    | exact resolve eq15307 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15307
  have eq15623 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq15310 eq268
    | exact resolve eq268 eq15310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15310
  have eq15664 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq15623 eq98
    | exact resolve eq98 eq15623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq15623
  have eq15691 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq15664
    | exact resolve eq15664 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15664
  have eq15694 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq15691
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq15691
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq15691
       have r₂ := eq13 y x
       grind)
    | exact resolve eq15691 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15691
  have eq15994 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq860 x y
       have i₂ := eq15694
       grind)
    | exact superpose eq15694 eq860
    | (have j0 := eq860 x y
       grind)
    | exact resolve eq860 eq15694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15996 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq15694
       grind)
    | exact superpose eq15694 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq15694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15694
  have eq15997 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15996
  have eq15999 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15994
  have eq16003 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15997
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15997
    | exact resolve eq15997 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15997
  have eq16004 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16003
  have eq16006 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15999
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15999
    | exact resolve eq15999 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15999
  have eq16019 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16006
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16006
    | exact resolve eq16006 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16006
  have eq16023 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq16019
    | exact resolve eq16019 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16019
  have eq16024 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq16023
  have eq16029 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16024
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16024
    | exact resolve eq16024 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16024
  have eq16033 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16029
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16029
    | exact resolve eq16029 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16029
  have eq16046 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq269 y x
       have i₂ := eq16004
       grind)
    | exact superpose eq16004 eq269
    | exact resolve eq269 eq16004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16004
  have eq16077 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16046
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16046
    | exact resolve eq16046 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16046
  have eq16080 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16077
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16077
    | exact resolve eq16077 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16077
  have eq16081 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16080
  have eq16132 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16033 eq269
    | exact resolve eq269 eq16033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16033
  have eq16163 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq16132
    | exact resolve eq16132 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16132
  have eq16166 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq16163
    | exact resolve eq16163 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16163
  have eq16167 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16166
  have eq16381 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq16081
       grind)
    | exact superpose eq16081 eq44
    | exact resolve eq44 eq16081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq16081
  have eq16403 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq16381
    | exact resolve eq16381 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16381
  have eq17699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16403 eq16167
    | exact resolve eq16167 eq16403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16167 eq16403
  have eq17706 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17699
  have eq17708 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17706
       have r₂ := eq27
       grind)
    | exact resolve eq17706 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17706
  have eq17730 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17708 eq248
    | exact resolve eq248 eq17708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq17708
  have eq18011 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17730 eq55
    | exact resolve eq55 eq17730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq17730
  have eq18043 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq18011
    | exact resolve eq18011 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq18011
  have eq18048 : x = (k x y) := by
    first
    | (have r₁ := eq18043
       have r₂ := eq50
       grind)
    | exact resolve eq18043 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq18043
  have eq18061 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq877 x y
       have i₂ := eq18048
       grind)
    | exact superpose eq18048 eq877
    | (have j0 := eq877 x y
       grind)
    | exact resolve eq877 eq18048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq18062 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq860 y x
       have i₂ := eq18048
       grind)
    | exact superpose eq18048 eq860
    | (have j0 := eq860 y x
       grind)
    | exact resolve eq860 eq18048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq18064 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18048
       grind)
    | exact superpose eq18048 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18065 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq18064
  have eq18067 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18062
  have eq18068 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18061
  have eq18071 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18065
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18065
    | exact resolve eq18065 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18065
  have eq18073 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18067
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18067
    | exact resolve eq18067 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18067
  have eq18074 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18068
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18068
    | exact resolve eq18068 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18068
  have eq18086 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18073
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18073
    | exact resolve eq18073 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18073
  have eq18087 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18074
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18074
    | exact resolve eq18074 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18074
  have eq18092 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq18086
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18086
    | exact resolve eq18086 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18086
  have eq18093 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18087
    | exact resolve eq18087 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18087
  have eq18097 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq18092
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18092
    | exact resolve eq18092 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18092
  have eq18098 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18093
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18093
    | exact resolve eq18093 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18093
  have eq18102 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18097
    | exact resolve eq18097 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18097
  have eq18103 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18098
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18098
    | exact resolve eq18098 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18098
  have eq18106 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18103
    | exact resolve eq18103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18103
  have eq18146 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18106 eq27
    | exact resolve eq27 eq18106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18106
  have eq20250 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq269 y x
       have i₂ := eq18071
       grind)
    | exact superpose eq18071 eq269
    | exact resolve eq269 eq18071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq20285 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20250
       have i₂ := eq18048
       grind)
    | exact superpose eq18048 eq20250
    | exact resolve eq20250 eq18048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18048 eq20250
  have eq20288 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20285
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20285
    | exact resolve eq20285 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20285
  have eq20290 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20288
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20288
    | exact resolve eq20288 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20288
  have eq20291 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq20290
  have eq20293 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20291 eq20
    | exact resolve eq20 eq20291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20291
  have eq20420 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20293
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20293
    | exact resolve eq20293 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20293
  have eq20612 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20420 eq26
    | exact resolve eq26 eq20420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20693 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20420 eq18146
    | (have r₁ := eq18146
       have r₂ := eq20420
       grind)
    | exact resolve eq18146 eq20420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18146
  have eq20695 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20693
  have eq21651 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18102 eq1290
    | exact resolve eq1290 eq18102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18102
  have eq21654 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq21651
    | (have j0 := eq21651 X0
       grind)
    | exact resolve eq21651 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21651
  have eq22980 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20612 eq1746
    | exact resolve eq1746 eq20612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746
  have eq23043 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22980
       have r₂ := eq27
       grind)
    | exact resolve eq22980 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22980
  have eq24899 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23043 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq23043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23043
  have eq24916 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq24899
  have eq27918 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20420 eq21654
    | exact resolve eq21654 eq20420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20420
  have eq28030 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq27918 X0
       grind)
    | (have r₁ := eq27918 X0
       have r₂ := eq27
       grind)
    | exact resolve eq27918 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27918
  have eq32454 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24916 eq28030
    | exact resolve eq28030 eq24916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24916 eq28030
  have eq32576 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq32454
  have eq32579 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20695 eq32576
    | exact resolve eq32576 eq20695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20695 eq32576
  have eq32647 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq32579
  have eq33075 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32647 eq20612
    | exact resolve eq20612 eq32647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20612 eq32647
  have eq33146 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq33075
  have eq33148 : x = (M.op x y) := by
    first
    | (have r₁ := eq33146
       have r₂ := eq27
       grind)
    | exact resolve eq33146 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33146
  have eq33452 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq33148 eq20
    | exact resolve eq20 eq33148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq33592 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq33452
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33452
    | exact resolve eq33452 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33452
  have eq33631 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq33592 eq26
    | exact resolve eq26 eq33592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq33653 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq33592 eq239
    | exact resolve eq239 eq33592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq33713 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq33592 eq1166
    | (have r₁ := eq1166
       have r₂ := eq33592
       grind)
    | exact resolve eq1166 eq33592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq33768 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq33713
  have eq36263 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq33768 eq1290
    | exact resolve eq1290 eq33768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36265 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq33768 eq36263
    | exact resolve eq36263 eq33768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36263
  have eq40430 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq33631 eq36265
    | exact resolve eq36265 eq33631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36265
  have eq40628 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40430 eq21654
    | exact resolve eq21654 eq40430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21654
  have eq40639 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq40430 eq263
    | exact resolve eq263 eq40430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq40430
  have eq40718 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq33768 eq40639
    | exact resolve eq40639 eq33768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33768 eq40639
  have eq40724 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33631 eq40628
    | exact resolve eq40628 eq33631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33631 eq40628
  have eq40725 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq40724
  have eq40752 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq40725 eq27
    | exact resolve eq27 eq40725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41191 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq40725 eq40718
    | exact resolve eq40718 eq40725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40718
  have eq41504 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq33653 eq41191
    | exact resolve eq41191 eq33653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33653 eq41191
  have eq41630 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq40725 eq41504
    | exact resolve eq41504 eq40725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40725 eq41504
  have eq41668 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq41630 eq268
    | exact resolve eq268 eq41630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq41630
  have eq41780 : (τ (σ y)) = (k y y) := by
    first
    | exact superpose eq41668 eq111
    | exact resolve eq111 eq41668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq41668
  have eq41831 : y = (k y y) := by
    first
    | exact superpose eq29 eq41780
    | exact resolve eq41780 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq41780
  have eq41858 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq41831
       grind)
    | exact superpose eq41831 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq41831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41831
  have eq41879 : y = (M.op y y) := by grind
  clear eq41858
  have eq41990 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq1290 y y X0
       have i₂ := eq41879
       grind)
    | exact superpose eq41879 eq1290
    | exact resolve eq1290 eq41879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq41992 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq41990 X0
       have i₂ := eq41879
       grind)
    | exact superpose eq41879 eq41990
    | exact resolve eq41990 eq41879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41879 eq41990
  have eq42098 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41992 x
       have i₂ := eq18071
       grind)
    | exact superpose eq18071 eq41992
    | exact resolve eq41992 eq18071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18071 eq41992
  have eq42269 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42098
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42098
    | exact resolve eq42098 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq42098
  have eq42270 : y = (M.op x y) := by grind
  clear eq42269
  have eq42285 : x = y := by
    first
    | exact superpose eq33148 eq42270
    | exact resolve eq42270 eq33148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33148 eq42270
  have eq42289 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq42285
       grind)
    | exact superpose eq42285 eq24
    | exact resolve eq24 eq42285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq42285
  have eq42433 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq42289
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42289
    | exact resolve eq42289 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq42289
  have eq42494 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq33592 eq42433
    | exact resolve eq42433 eq33592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33592 eq42433
  have eq42542 : False := by grind
  exact eq42542

/-- `Equation3081`: `x = (((x ◇ y) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_pyx_Equation3081 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3081 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3081.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  clear eq32 eq34
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq77 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq202 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq188
  have eq208 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq202 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq202 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq202 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq202
  have eq362 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq208
    | exact resolve eq208 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq208 (σ X1) X0
       grind)
    | exact superpose eq208 eq15
    | (have j1 := eq208 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq393 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq362 (τ X0) X1
       grind)
    | exact superpose eq362 eq19
    | (have j1 := eq362 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq362
  have eq689 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq393 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq393
    | exact resolve eq393 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq722 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq689 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq689
    | (have j0 := eq689 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq689 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq2376 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq370 x y
       grind)
    | exact superpose eq370 eq16
    | (have j1 := eq370 x y
       grind)
    | exact resolve eq16 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq2429 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2376
       have i₂ := eq722 x y
       grind)
    | exact superpose eq722 eq2376
    | (have j1 := eq722 (σ x) (σ y)
       grind)
    | (have r₁ := eq2376
       have r₂ := eq722 x y
       grind)
    | (have r₁ := eq2376
       have r₂ := eq722 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2376
       have r₂ := eq722 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2376 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq2376
  have eq2430 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2429
  have eq2504 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2430
       grind)
    | exact superpose eq2430 eq10
    | exact resolve eq10 eq2430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2430
  have eq2550 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2504
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2504
    | exact resolve eq2504 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504
  have eq2551 : x = y := by grind
  clear eq2550
  have eq2553 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2551
       grind)
    | exact superpose eq2551 eq16
    | exact resolve eq16 eq2551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551
  have eq2554 : False := by grind
  exact eq2554
