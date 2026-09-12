import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pyx_pyy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq24 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq24 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X0 (k X0 X0)
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X1 (k X1 X1)
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq35 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq40 X1 (k X1 X1)
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq41 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq41 X0 (M.op X1 (M.op X0 X0))
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq41 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq47
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq42 X0 X1
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq42 X0 X1
       grind)
    | (have r₁ := eq51 X0 (M.op X0 X0)
       have r₂ := eq42 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq42 X0 (k X1 X0)
       grind)
    | exact resolve eq51 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq51
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq132 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq136 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       have j1 := eq62 X1 X0
       grind)
    | (have r₁ := eq132 X1 X0
       have r₂ := eq62 X0 X1
       grind)
    | (have r₁ := eq132 X1 X1
       have r₂ := eq62 X1 X1
       grind)
    | exact resolve eq132 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq132
  have eq321 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq136 (σ X1) (σ X0)
       grind)
    | exact superpose eq136 eq15
    | exact resolve eq15 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq321 X0 X1
       have i₂ := eq136 X1 X0
       grind)
    | exact superpose eq136 eq321
    | exact resolve eq321 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq321
  have eq331 : False := by grind
  exact eq331

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pxx_x_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq9 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq34 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) X1) = X1 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq87 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (k X3 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq35 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq9 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq35 X0 X1 X2
       grind)
    | exact superpose eq35 eq12
    | exact resolve eq12 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 ∨ (M.op X0 X3) = (k X3 X0) ∨ (M.op X0 X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X0
       have i₂ := eq35 X0 X1 X2
       grind)
    | exact superpose eq35 eq14
    | (have j0 := eq14 X3 X0
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) ≠ X0 ∨ (M.op X0 X3) = X3 ∨ (k X3 X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X0
       have i₂ := eq35 X0 X1 X2
       grind)
    | exact superpose eq35 eq13
    | (have j0 := eq13 X3 X0
       grind)
    | exact resolve eq13 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X1) X0))) X2) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0)) X3
       have i₂ := eq23 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq24 (M.op X0 X0) x x X3
       have i₂ := eq23 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq24
  have eq160 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X0 X0)) X2) X3) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq132 X0 x X2 X3
       have i₂ := eq139 x X0
       grind)
    | (have i₁ := eq132 X0 x X2 X3
       have i₂ := eq139 X0 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq139 eq132
    | exact resolve eq132 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq178 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X1 X1)
       have i₂ := eq139 X1 X0
       grind)
    | exact superpose eq139 eq12
    | (have j0 := eq12 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq12 x (M.op X0 X0)
       have r₂ := eq139 X0 x
       grind)
    | exact resolve eq12 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq262 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 (M.op X0 X0)
       have i₂ := eq189 (M.op X0 X0) X1
       grind)
    | exact superpose eq189 eq139
    | exact resolve eq139 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq189 (τ X0) X1
       grind)
    | exact superpose eq189 eq17
    | exact resolve eq17 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq308 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (M.op (M.op (σ X0) (σ X0)) (σ X0)) X2) = X2 ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq60 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq60 eq15
    | (have j1 := eq60 (σ X0) X2 (σ X1)
       grind)
    | exact resolve eq15 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq323 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = X2 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq308 X0 X1 X2
       have i₂ := eq139 (σ X0) (σ X0)
       grind)
    | (have i₁ := eq308 X0 X1 X2
       have i₂ := eq139 X0 (M.op (M.op (σ X0) (σ X0)) (σ X0))
       grind)
    | exact superpose eq139 eq308
    | (have j0 := eq308 X0 X1 X2
       grind)
    | exact resolve eq308 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq520 : ∀ X0 X1 X2 : G, (k (σ X0) (M.op (M.op X1 (M.op X2 X1)) X2)) = (σ (k X0 X0)) ∨ (σ X0) = (k (σ X0) (M.op (M.op X1 (M.op X2 X1)) X2)) ∨ (σ X0) = (k (σ X0) (M.op (M.op X1 (M.op X2 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X0
       have i₂ := eq35 (σ X0) X1 X2
       grind)
    | exact superpose eq35 eq62
    | exact resolve eq62 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq527 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62 x y
       grind)
    | exact superpose eq62 eq16
    | (have j1 := eq62 x x
       grind)
    | exact resolve eq16 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq557 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq573 : ∀ X0 X1 X2 : G, (k (σ X0) (M.op (M.op X1 (M.op X2 X1)) X2)) = (σ (k X0 X0)) ∨ (σ X0) = (k (σ X0) (M.op (M.op X1 (M.op X2 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq520 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq1898 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq559 (M.op X0 X0)
       have i₂ := eq262 X0 X0
       grind)
    | exact superpose eq262 eq559
    | (have j0 := eq559 (M.op X0 X0)
       grind)
    | exact resolve eq559 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq559
  have eq1903 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1898 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq2514 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X4 (k X0 (M.op (M.op X1 (M.op (M.op X2 (M.op X3 X2)) X3)) X1))) X4) X5) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq160 X0 X4 X5
       have i₂ := eq87 X1 X2 X3 X0
       grind)
    | exact superpose eq87 eq160
    | exact resolve eq160 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq160
  have eq14012 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq139 (σ (M.op X0 X0)) X1
       have i₂ := eq1903 X0
       grind)
    | exact superpose eq1903 eq139
    | exact resolve eq139 eq1903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14020 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq189 X1 (σ (M.op X0 X0))
       have i₂ := eq1903 X0
       grind)
    | exact superpose eq1903 eq189
    | exact resolve eq189 eq1903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq14700 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14012 (M.op (M.op X0 (M.op X1 X0)) X1) X2
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq14012
    | exact resolve eq14012 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14012
  have eq16141 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq267 X0 x
       have i₂ := eq14020 x X0
       grind)
    | exact superpose eq14020 eq267
    | exact resolve eq267 eq14020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq14020
  have eq18270 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16141 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16141
    | exact resolve eq16141 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18322 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq16141 X0
       grind)
    | exact superpose eq16141 eq10
    | exact resolve eq10 eq16141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16141
  have eq19943 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq62 X0 X0
       have i₂ := eq18270 X0
       grind)
    | exact superpose eq18270 eq62
    | exact resolve eq62 eq18270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq20034 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq18270 X0
       grind)
    | exact superpose eq18270 eq12
    | exact resolve eq12 eq18270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18270
  have eq20062 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq19943 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19943
  have eq20076 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) ≠ (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20034 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq20034
    | (have j0 := eq20034 X0
       grind)
    | exact resolve eq20034 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20034
  have eq20131 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq20076 X0
       have j1 := eq20062 X0
       grind)
    | (have r₁ := eq20076 X0
       have r₂ := eq20062 X0
       grind)
    | exact resolve eq20076 eq20062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20062 eq20076
  have eq20543 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq20131 X0
       grind)
    | exact superpose eq20131 eq10
    | exact resolve eq10 eq20131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20131
  have eq20577 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq20543 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq20543
    | exact resolve eq20543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20543
  have eq23857 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq139 (τ X0) X1
       have i₂ := eq18322 X0
       grind)
    | exact superpose eq18322 eq139
    | exact resolve eq139 eq18322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18322
  have eq25061 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23857 (M.op (M.op X0 (M.op X1 X0)) X1) X2
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq23857
    | exact resolve eq23857 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23857
  have eq36284 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq323 X0 X1 (σ X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq36286 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36284 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36284
  have eq46052 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = (σ (k (τ X0) (τ X0))) ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq573 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq573
    | exact resolve eq573 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq46596 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = (k (σ (τ X0)) X0) ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46052 X0 X1 X2
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq46052
    | (have j0 := eq46052 X0 X1 X2
       grind)
    | exact resolve eq46052 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq46052
  have eq46714 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = (k X0 X0) ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46596 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46596
    | (have j0 := eq46596 X0 X1 X2
       grind)
    | exact resolve eq46596 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46596
  have eq46763 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq46714 X0 X1 X2
       have j1 := eq89 X0 X1 X2
       grind)
    | (have r₁ := eq46714 X0 X1 X2
       have r₂ := eq89 X0 X1 X2
       grind)
    | exact resolve eq46714 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq46714
  have eq66736 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X1)) X0)) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46763 X2 (M.op X1 X1) X0
       have i₂ := eq139 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq139 eq46763
    | exact resolve eq46763 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46763
  have eq76071 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq36286 (τ X1) (τ X0)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq36286
    | (have j0 := eq36286 (τ X1) (τ X0)
       grind)
    | exact resolve eq36286 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq36286
  have eq76114 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq76071 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq76071
    | (have j0 := eq76071 X0 X1
       grind)
    | exact resolve eq76071 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76071
  have eq76142 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq76114 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq76114
    | (have j0 := eq76114 X0 X1
       grind)
    | exact resolve eq76114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76114
  have eq76150 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq76142 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq76142
    | (have j0 := eq76142 X0 X1
       grind)
    | exact resolve eq76142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76142
  have eq76152 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq76150 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq76150
    | (have j0 := eq76150 X0 X1
       grind)
    | exact resolve eq76150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76150
  have eq139295 : ∀ X0 X2 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X2) = X2 ∨ (k X2 X0) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq92 X0 x x X2
       have i₂ := eq66736 x x X0
       grind)
    | (have i₁ := eq92 (M.op (M.op x (M.op X2 x)) X2) x X2 x
       have i₂ := eq66736 X0 x (M.op (M.op x (M.op X2 x)) X2)
       grind)
    | exact superpose eq66736 eq92
    | (have j0 := eq92 X0 x X2 X2
       grind)
    | exact resolve eq92 eq66736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq66736
  have eq139719 : ∀ X0 X2 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X2) = X2 := by
    intro X0 X2
    first
    | (have j0 := eq139295 X0 X2
       have j1 := eq76152 X0 X0
       grind)
    | (have r₁ := eq139295 x X0
       have r₂ := eq76152 X0 x
       grind)
    | exact resolve eq139295 eq76152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76152 eq139295
  have eq139995 : ∀ X0 X2 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq139719 X0 X2
       have i₂ := eq20577 X0
       grind)
    | exact superpose eq20577 eq139719
    | (have j0 := eq139719 X0 X2
       grind)
    | exact resolve eq139719 eq20577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20577 eq139719
  have eq140589 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) ≠ X0 ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139995 X0 X2
       have i₂ := eq189 X0 X1
       grind)
    | exact superpose eq189 eq139995
    | (have j0 := eq139995 X0 X2
       grind)
    | exact resolve eq139995 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq148670 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (k X5 (M.op (M.op X0 (k X1 (M.op (M.op X2 (M.op (M.op X3 (M.op X4 X3)) X4)) X2))) X0)) ≠ X5 ∨ (M.op X5 X6) = X6 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq140589 X5 (M.op (M.op X0 (k X1 (M.op (M.op X2 (M.op (M.op X3 (M.op X4 X3)) X4)) X2))) X0) X6
       have i₂ := eq2514 X1 X2 X3 X4 X0 (M.op (M.op X0 (k X1 (M.op (M.op X2 (M.op (M.op X3 (M.op X4 X3)) X4)) X2))) X0)
       grind)
    | exact superpose eq2514 eq140589
    | (have j0 := eq140589 X5 X1 X6
       grind)
    | exact resolve eq140589 eq2514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140589
  have eq148683 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (k X1 (M.op (M.op X0 X0) (M.op (M.op X2 (k X3 (M.op (M.op X4 (M.op (M.op X5 (M.op X6 X5)) X6)) X4))) X2))) = X1 ∨ (M.op X1 X7) = (k X7 X1) ∨ (M.op X1 X7) = X7 := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq91 X1 X0 (M.op (M.op X2 (k X3 (M.op (M.op X4 (M.op (M.op X5 (M.op X6 X5)) X6)) X4))) X2) X7
       have i₂ := eq2514 X3 X4 X5 X6 X2 X0
       grind)
    | exact superpose eq2514 eq91
    | (have j0 := eq91 X1 X1 X2 X7
       grind)
    | exact resolve eq91 eq2514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq2514
  have eq148958 : ∀ X1 X2 X3 X4 X5 X6 X7 : G, (k X1 (M.op (M.op X2 (k X3 (M.op (M.op X4 (M.op (M.op X5 (M.op X6 X5)) X6)) X4))) X2)) = X1 ∨ (M.op X1 X7) = (k X7 X1) ∨ (M.op X1 X7) = X7 := by
    intro X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq148683 x X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq139 x (M.op (M.op X2 (k X3 (M.op (M.op X4 (M.op (M.op X5 (M.op X6 X5)) X6)) X4))) X2)
       grind)
    | (have i₁ := eq148683 x X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq139 x (M.op (M.op x x) (M.op (M.op X2 (k X3 (M.op (M.op X4 (M.op (M.op X5 (M.op X6 X5)) X6)) X4))) X2))
       grind)
    | exact superpose eq139 eq148683
    | (have j0 := eq148683 x X1 X2 X3 X4 X5 X6 X7
       grind)
    | exact resolve eq148683 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148683
  have eq149498 : ∀ X1 X7 : G, (M.op X1 X7) = (k X7 X1) ∨ (M.op X1 X7) = X7 := by
    intro X1 X7
    first
    | (have j0 := eq148958 X1 x x x x x X7
       have j1 := eq148670 x X1 x x x X1 X7
       grind)
    | (have r₁ := eq148958 x x X1 x x x X7
       have r₂ := eq148670 x X1 x x x x x
       grind)
    | exact resolve eq148958 eq148670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148670 eq148958
  have eq150010 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq527
       have i₂ := eq149498 x y
       grind)
    | exact superpose eq149498 eq527
    | (have j1 := eq149498 (σ x) (σ x)
       grind)
    | exact resolve eq527 eq149498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq149498
  have eq150011 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq150010
  have eq150052 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq139995 (σ x) (σ y)
       grind)
    | (have r₁ := eq150011
       have r₂ := eq139995 (σ x) x
       grind)
    | exact resolve eq150011 eq139995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139995 eq150011
  have eq152143 : ∀ X0 : G, (M.op (τ (M.op (M.op (σ y) (σ y)) (σ x))) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25061 (σ y) (σ x) X0
       have i₂ := eq150052
       grind)
    | exact superpose eq150052 eq25061
    | exact resolve eq25061 eq150052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25061 eq150052
  have eq152149 : ∀ X0 : G, (M.op (τ (σ x)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq152143 X0
       have i₂ := eq139 (σ y) (σ x)
       grind)
    | (have i₁ := eq152143 X0
       have i₂ := eq139 X0 (M.op (M.op (σ y) (σ y)) (σ x))
       grind)
    | exact superpose eq139 eq152143
    | exact resolve eq152143 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152143
  have eq152203 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq152149 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq152149
    | exact resolve eq152149 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152149
  have eq154190 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq152203 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152203
  have eq154191 : y = (M.op x y) := by grind
  clear eq154190
  have eq156171 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14700 y x X0
       have i₂ := eq154191
       grind)
    | exact superpose eq154191 eq14700
    | exact resolve eq14700 eq154191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14700
  have eq156179 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq156171 X0
       have i₂ := eq139 y x
       grind)
    | (have i₁ := eq156171 X0
       have i₂ := eq139 X0 (M.op (M.op y y) x)
       grind)
    | exact superpose eq139 eq156171
    | exact resolve eq156171 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq156171
  have eq163984 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq156179 (σ y)
       grind)
    | exact superpose eq156179 eq16
    | exact resolve eq16 eq156179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156179
  have eq164611 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq163984
       have i₂ := eq154191
       grind)
    | exact superpose eq154191 eq163984
    | exact resolve eq163984 eq154191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154191 eq163984
  have eq164612 : False := by grind
  exact eq164612

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pyx_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
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
  have eq63 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq64 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
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
  clear eq22 eq36
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq68 y x
       grind)
    | exact superpose eq68 eq74
    | (have j1 := eq68 x x
       grind)
    | exact resolve eq74 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq448 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op X0 X0) x x X3
       have i₂ := eq52 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq869 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq96 eq68
    | (have j0 := eq68 x (σ x)
       grind)
    | exact resolve eq68 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq869
    | exact resolve eq869 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq873 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq870
       have r₂ := eq27
       grind)
    | exact resolve eq870 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq882 : ∀ X0 : G, x = (M.op x x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq873 eq448
    | exact resolve eq448 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq905 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq448 x X0
       have i₂ := eq882 X1
       grind)
    | exact superpose eq882 eq448
    | (have j1 := eq882 X1
       grind)
    | exact resolve eq448 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq1023 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq905
    | (have j0 := eq905 X0 (σ y)
       grind)
    | exact resolve eq905 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq1111 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1023 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1023
    | (have j0 := eq1023 y
       grind)
    | exact resolve eq1023 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1150 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1111 eq64
    | (have r₁ := eq64
       have r₂ := eq1111
       grind)
    | exact resolve eq64 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq1151 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1111 eq27
    | exact resolve eq27 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1152 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1150
  have eq1257 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1152 eq96
    | exact resolve eq96 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq1152
  have eq1262 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1257
       have r₂ := eq1151
       grind)
    | exact resolve eq1257 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151 eq1257
  have eq1413 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq448 x X0
       have i₂ := eq1262
       grind)
    | exact superpose eq1262 eq448
    | exact resolve eq448 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1448 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1413 y
       grind)
    | exact superpose eq1413 eq18
    | (have j1 := eq1413 y
       grind)
    | exact resolve eq18 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1413
  have eq1475 : y = (M.op x y) := by grind
  clear eq1448
  have eq1535 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1475 eq20
    | exact resolve eq20 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1538 : y ≠ y ∨ y = (k y x) := by
    first
    | exact superpose eq1475 eq63
    | (have r₁ := eq63
       have r₂ := eq1475
       grind)
    | exact resolve eq63 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1475
  have eq1549 : y = (k y x) := by grind
  clear eq1538
  have eq1562 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1535
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1535
    | exact resolve eq1535 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1563 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1562 eq26
    | exact resolve eq26 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1589 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq1549
       grind)
    | exact superpose eq1549 eq74
    | exact resolve eq74 eq1549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1549
  have eq1592 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1562 eq1589
    | exact resolve eq1589 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589
  have eq1594 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1592
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1592
    | exact resolve eq1592 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1592
  have eq1595 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1562 eq1594
    | exact resolve eq1594 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562 eq1594
  have eq1672 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1595 eq68
    | (have j0 := eq68 x (σ x)
       grind)
    | exact resolve eq68 eq1595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1595
  have eq1673 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1563 eq1672
    | exact resolve eq1672 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq1676 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq1673
       have r₂ := eq27
       grind)
    | exact resolve eq1673 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq1780 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1676 eq448
    | exact resolve eq448 eq1676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448 eq1676
  have eq1803 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1780 eq1563
    | exact resolve eq1563 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563 eq1780
  have eq1846 : False := by grind
  exact eq1846

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_x_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X1)) X2) ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 (M.op X2 X1)) X2) (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq9 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq39 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq39 eq9
    | exact resolve eq9 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq84 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 x (M.op X0 X0)
       have i₂ := eq71 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq71 eq9
    | exact resolve eq9 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (M.op X1 (M.op X2 X1)) X2) = X0 ∨ (M.op X0 X0) = (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq184 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq122 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq122
    | (have j0 := eq122 (σ X0)
       grind)
    | exact resolve eq122 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq509 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ (M.op (M.op X2 (M.op X3 X2)) X3) = (M.op X0 (M.op (M.op X1 X1) X0)) ∨ (M.op X0 (M.op (M.op X1 X1) X0)) = (k (M.op X0 (M.op (M.op X1 X1) X0)) (M.op (M.op X2 (M.op X3 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq114 (M.op X0 (M.op (M.op X1 X1) X0)) X1 X2
       have i₂ := eq71 X0 X1 (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq71 eq114
    | (have j0 := eq114 (M.op X0 (M.op (M.op X1 X1) X0)) X2 X3
       grind)
    | (have r₁ := eq114 (M.op X0 (M.op (M.op X1 X1) X0)) X1 X2
       have r₂ := eq71 X0 X1 (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact resolve eq114 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq512 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X2)) X3) = (M.op X0 (M.op (M.op X1 X1) X0)) ∨ (M.op X0 (M.op (M.op X1 X1) X0)) = (k (M.op X0 (M.op (M.op X1 X1) X0)) (M.op (M.op X2 (M.op X3 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq509 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq518 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (k (M.op X0 (M.op (M.op X1 X1) X0)) (M.op (M.op X2 (M.op X3 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq512 X0 X1 X2 X3
       have j1 := eq41 (M.op X0 (M.op (M.op X1 X1) X0)) X2 X3
       grind)
    | (have r₁ := eq512 X0 X1 X1 X2
       have r₂ := eq41 (M.op X0 (M.op (M.op X1 X1) X0)) X1 X2
       grind)
    | exact resolve eq512 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq512
  have eq523 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X2 (M.op X3 X2)) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq518 X2 X0 X2 X3
       have i₂ := eq84 X0 X2
       grind)
    | (have i₁ := eq518 X0 x X2 X3
       have i₂ := eq84 X0 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq84 eq518
    | exact resolve eq518 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq627 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq176 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq176 X0 X1
       grind)
    | exact superpose eq176 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq176 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq176 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq176 X1 X1
       grind)
    | exact resolve eq13 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq176 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq176 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq648 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq627 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq654 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq648 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq648
    | (have j0 := eq648 X0 X1
       grind)
    | exact resolve eq648 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq790 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X1 x (M.op X0 X0)
       have i₂ := eq71 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq71 eq523
    | exact resolve eq523 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq523
  have eq970 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq184 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq984 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq970 (M.op X0 X0)
       have i₂ := eq790 X0 X0
       grind)
    | exact superpose eq790 eq970
    | (have j0 := eq970 (M.op X0 X0)
       grind)
    | exact resolve eq970 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq970 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq970
    | (have j0 := eq970 (τ X0)
       grind)
    | exact resolve eq970 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq993 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq984 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq999 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq988 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq988
    | (have j0 := eq988 X0
       grind)
    | exact resolve eq988 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1006 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq999 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq999
    | (have j0 := eq999 X0
       grind)
    | exact resolve eq999 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1014 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1006 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq1006
    | (have j0 := eq1006 (τ X0)
       grind)
    | exact resolve eq1006 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq1041 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ (M.op X0 X0)) X1
       have i₂ := eq993 X0
       grind)
    | exact superpose eq993 eq84
    | exact resolve eq84 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1070 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1041 (M.op (M.op X0 (M.op X1 X0)) X1) X2
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq1041
    | exact resolve eq1041 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq6858 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1014 (M.op X0 X0)
       have i₂ := eq790 X0 X0
       grind)
    | exact superpose eq790 eq1014
    | (have j0 := eq1014 (M.op X0 X0)
       grind)
    | exact resolve eq1014 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq1014
  have eq6871 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq6858 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6858
  have eq6923 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (τ (M.op X0 X0)) X1
       have i₂ := eq6871 X0
       grind)
    | exact superpose eq6871 eq84
    | exact resolve eq84 eq6871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6871
  have eq14738 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq654 X0 X1
       have j1 := eq646 X1 X0
       grind)
    | (have r₁ := eq654 X1 X1
       have r₂ := eq646 (k X1 X1) X1
       grind)
    | (have r₁ := eq654 X1 X0
       have r₂ := eq646 X0 X1
       grind)
    | (have r₁ := eq654 X1 X1
       have r₂ := eq646 (k X1 X1) X1
       grind)
    | exact resolve eq654 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq654
  have eq14739 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq14738 X0 X1
       have j1 := eq645 X1 X0
       grind)
    | (have r₁ := eq14738 X1 X0
       have r₂ := eq645 X0 X1
       grind)
    | (have r₁ := eq14738 X1 X1
       have r₂ := eq645 X1 X1
       grind)
    | exact resolve eq14738 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq14738
  have eq14740 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14739 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14739
    | exact resolve eq14739 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14781 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14739 y x
       grind)
    | exact superpose eq14739 eq16
    | (have j1 := eq14739 y x
       grind)
    | exact resolve eq16 eq14739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14877 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) (σ (k X0 X1))) (σ X1)) X2) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq14739 X0 X1
       grind)
    | exact superpose eq14739 eq9
    | (have j1 := eq14739 X0 X1
       grind)
    | exact resolve eq9 eq14739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14902 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14739 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14739
  have eq14950 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14740 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq14740
    | (have j0 := eq14740 X0 X1
       grind)
    | exact resolve eq14740 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq14740
  have eq21839 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14902 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq14902
    | (have j0 := eq14902 (τ X1) (τ X0)
       grind)
    | exact resolve eq14902 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14902
  have eq21859 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21839 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq21839
    | (have j0 := eq21839 X0 X1
       grind)
    | exact resolve eq21839 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21839
  have eq21878 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21859 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq21859
    | (have j0 := eq21859 X0 X1
       grind)
    | exact resolve eq21859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21859
  have eq21885 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21878 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21878
    | (have j0 := eq21878 X0 X1
       grind)
    | exact resolve eq21878 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21878
  have eq21890 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21885 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21885
    | (have j0 := eq21885 X0 X1
       grind)
    | exact resolve eq21885 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21885
  have eq21933 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14950 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14950
    | exact resolve eq14950 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14950
  have eq22057 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14781
       have i₂ := eq21933 y x
       grind)
    | exact superpose eq21933 eq14781
    | (have j1 := eq21933 (σ y) (σ x)
       grind)
    | exact resolve eq14781 eq21933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14781
  have eq22060 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22057
  have eq22063 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22060
       grind)
    | exact superpose eq22060 eq16
    | exact resolve eq16 eq22060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22065 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq22060
       grind)
    | exact superpose eq22060 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq22060
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq22060
       grind)
    | exact resolve eq12 eq22060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22091 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq22065
  have eq22093 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22091
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq22091
    | exact resolve eq22091 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22091
  have eq22100 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq22093
       grind)
    | exact superpose eq22093 eq10
    | exact resolve eq10 eq22093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22093
  have eq22138 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22100
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq22100
    | exact resolve eq22100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22100
  have eq22139 : y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq22138
       have r₂ := eq12 y x
       grind)
    | exact resolve eq22138 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22138
  have eq22140 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22139
       have i₂ := eq21933 y x
       grind)
    | exact superpose eq21933 eq22139
    | (have j1 := eq21933 y x
       grind)
    | exact resolve eq22139 eq21933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21933
  have eq22145 : x ≠ y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21890 y x
       have i₂ := eq22139
       grind)
    | exact superpose eq22139 eq21890
    | (have j0 := eq21890 y x
       grind)
    | exact resolve eq21890 eq22139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21890
  have eq22147 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22063
       have i₂ := eq22140
       grind)
    | exact superpose eq22140 eq22063
    | exact resolve eq22063 eq22140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22063
  have eq22169 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1070 y x X0
       have i₂ := eq22140
       grind)
    | exact superpose eq22140 eq1070
    | exact resolve eq1070 eq22140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq22140
  have eq22181 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22169 X0
       have i₂ := eq84 y x
       grind)
    | (have i₁ := eq22169 X0
       have i₂ := eq84 X0 (M.op (M.op y y) x)
       grind)
    | exact superpose eq84 eq22169
    | exact resolve eq22169 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22169
  have eq22201 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22147
       have r₂ := eq22145
       grind)
    | exact resolve eq22147 eq22145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22145 eq22147
  have eq22639 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22060
       have i₂ := eq22181 (σ y)
       grind)
    | exact superpose eq22181 eq22060
    | exact resolve eq22060 eq22181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22060 eq22181
  have eq22837 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq22639
  have eq22941 : x = (M.op x y) := by
    first
    | (have r₁ := eq22837
       have r₂ := eq22201
       grind)
    | exact resolve eq22837 eq22201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22201 eq22837
  have eq37209 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ y)) (σ x)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14877 y x X0
       have i₂ := eq22139
       grind)
    | exact superpose eq22139 eq14877
    | (have j0 := eq14877 y x x
       grind)
    | exact resolve eq14877 eq22139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14877 eq22139
  have eq37600 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37209 X0
       have i₂ := eq84 (σ y) (σ x)
       grind)
    | (have i₁ := eq37209 X0
       have i₂ := eq84 X0 (M.op (M.op (σ y) (σ y)) (σ x))
       grind)
    | exact superpose eq84 eq37209
    | exact resolve eq37209 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq37209
  have eq37669 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq37600 X0
       grind)
    | exact superpose eq37600 eq16
    | (have j1 := eq37600 X0
       grind)
    | exact resolve eq16 eq37600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37600
  have eq37704 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37669 X0
       have i₂ := eq22941
       grind)
    | exact superpose eq22941 eq37669
    | (have j0 := eq37669 X0
       grind)
    | exact resolve eq37669 eq22941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37669
  have eq37705 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq37704 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37704
  have eq37792 : ∀ X0 : G, (M.op (τ (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6923 (σ x) X0
       have i₂ := eq37705 (σ x)
       grind)
    | exact superpose eq37705 eq6923
    | exact resolve eq6923 eq37705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6923
  have eq38058 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37792 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq37792
    | exact resolve eq37792 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37792
  have eq38111 : x = y := by
    first
    | (have i₁ := eq38058 y
       have i₂ := eq22941
       grind)
    | exact superpose eq22941 eq38058
    | exact resolve eq38058 eq22941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22941
  have eq38439 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38111
       grind)
    | exact superpose eq38111 eq16
    | exact resolve eq16 eq38111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38111
  have eq38496 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq38439
       have i₂ := eq37705 (σ x)
       grind)
    | exact superpose eq37705 eq38439
    | exact resolve eq38439 eq37705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37705 eq38439
  have eq38497 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq38496
       have i₂ := eq38058 x
       grind)
    | exact superpose eq38058 eq38496
    | exact resolve eq38496 eq38058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38058 eq38496
  have eq38498 : False := by grind
  exact eq38498

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  clear eq19
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq9 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq64 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq66 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq69 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq66 X1 X2 (σ X0)
       grind)
    | exact superpose eq66 eq29
    | exact resolve eq29 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq70 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq66 X1 X2 (τ X0)
       grind)
    | exact superpose eq66 eq18
    | exact resolve eq18 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq71 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq69
    | exact resolve eq69 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq140 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq62 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq177 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66 x (M.op X0 X0) X1
       have i₂ := eq140 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq140 eq66
    | exact resolve eq66 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq178 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 X1 x (M.op X0 X0)
       have i₂ := eq140 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq140 eq71
    | exact resolve eq71 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq179 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 x (M.op X0 X0)
       have i₂ := eq140 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq140 eq72
    | exact resolve eq72 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq140
  have eq388 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq388
    | (have j0 := eq388 (σ X0) (σ X1)
       grind)
    | exact resolve eq388 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) X0) = X0 ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 (σ (M.op X1 X1))
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq388
    | (have j0 := eq388 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq388 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1929 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq400 X1 X0
       have i₂ := eq388 X1 X0
       grind)
    | exact superpose eq388 eq400
    | (have j0 := eq400 X1 X0
       have j1 := eq388 (σ X1) (σ X0)
       grind)
    | exact resolve eq400 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq11268 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ (M.op X0 X0))
       have i₂ := eq406 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq406 eq12
    | (have j0 := eq12 X1 (σ (M.op X0 X0))
       have j1 := eq406 (σ (M.op X0 X0)) X0
       grind)
    | (have r₁ := eq12 X0 (σ (M.op X1 X1))
       have r₂ := eq406 (σ (M.op X1 X1)) X1
       grind)
    | exact resolve eq12 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq11349 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq11268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11268
  have eq11403 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq11349 X0 X1
       have j1 := eq12 X1 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq11349 X0 X1
       have r₂ := eq12 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq11349 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11349
  have eq11423 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11403 X0 X1
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq11403
    | exact resolve eq11403 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq11403
  have eq28328 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1929 x y
       grind)
    | exact superpose eq1929 eq16
    | (have j1 := eq1929 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1929 x y
       grind)
    | exact resolve eq16 eq1929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1929
  have eq28454 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq28328
  have eq28510 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq179 (σ y) X0
       have i₂ := eq28454
       grind)
    | exact superpose eq28454 eq179
    | exact resolve eq179 eq28454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq28454
  have eq28591 : ∀ X0 : G, x = (M.op y y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq28510 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28510
    | exact resolve eq28510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28510
  have eq28598 : ∀ X0 X1 : G, (k X1 x) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177 y X1
       have i₂ := eq28591 X0
       grind)
    | exact superpose eq28591 eq177
    | (have j1 := eq28591 X1
       grind)
    | exact resolve eq177 eq28591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq28591
  have eq28838 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq28598 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28598
  have eq28839 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq28838 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28838
  have eq28889 : ∀ X0 : G, (M.op x X0) = X0 ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq28839 X0
       have i₂ := eq388 X0 x
       grind)
    | exact superpose eq388 eq28839
    | (have j1 := eq388 X0 x
       grind)
    | exact resolve eq28839 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq30216 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq28889 x
       grind)
    | exact superpose eq28889 eq12
    | (have j0 := eq12 X0 x
       have j1 := eq28889 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq28889 x
       grind)
    | exact resolve eq12 eq28889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30360 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq28889 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28889
  have eq30361 : x = (M.op x x) := by grind
  clear eq30360
  have eq30363 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq30216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30216
  have eq30478 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq30363 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq30363 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq30363 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30363
  have eq30499 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30478 X0
       have i₂ := eq28839 X0
       grind)
    | exact superpose eq28839 eq30478
    | exact resolve eq30478 eq28839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28839 eq30478
  have eq30531 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11423 x X0
       have i₂ := eq30361
       grind)
    | exact superpose eq30361 eq11423
    | exact resolve eq11423 eq30361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11423 eq30361
  have eq30600 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30499 y
       grind)
    | exact superpose eq30499 eq16
    | exact resolve eq16 eq30499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30499
  have eq31053 : False := by grind
  exact eq31053

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  clear eq36
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq108
    | exact resolve eq108 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq374 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq52 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq374 (M.op X0 X0) x X1
       have i₂ := eq52 x (M.op X0 X0) X0
       grind)
    | exact superpose eq52 eq374
    | exact resolve eq374 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq374
  have eq674 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  have eq764 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq14591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq14591
    | exact resolve eq14591 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14591
  have eq14603 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq14592
       have r₂ := eq28
       grind)
    | exact resolve eq14592 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14592
  have eq14605 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq14603
    | exact resolve eq14603 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14603
  have eq14610 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq14605
  have eq14678 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq14610
    | exact resolve eq14610 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14610
  have eq15087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14678 eq111
    | exact resolve eq111 eq14678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14678
  have eq15097 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15087
  have eq15099 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15097
       have r₂ := eq28
       grind)
    | exact resolve eq15097 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15097
  have eq15106 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15099
  have eq15175 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15106
    | exact resolve eq15106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15106
  have eq15591 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq15175
       grind)
    | exact superpose eq15175 eq45
    | exact resolve eq45 eq15175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15175
  have eq15609 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq15591
    | exact resolve eq15591 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15591
  have eq15754 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15609 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq15609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15757 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15754
    | exact resolve eq15754 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15754
  have eq15768 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15757
       have r₂ := eq28
       grind)
    | exact resolve eq15757 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15757
  have eq15770 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15768
    | exact resolve eq15768 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15768
  have eq15771 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15770
  have eq15778 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15771
  have eq15849 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq15778
    | exact resolve eq15778 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15778
  have eq16265 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15849 eq15609
    | exact resolve eq15609 eq15849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15609 eq15849
  have eq16269 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16265
  have eq16273 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16269
       have r₂ := eq28
       grind)
    | exact resolve eq16269 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16269
  have eq16275 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16273 eq28
    | exact resolve eq28 eq16273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16276 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16273 eq72
    | (have r₁ := eq72
       have r₂ := eq16273
       grind)
    | exact resolve eq72 eq16273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq16273
  have eq16280 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16276
  have eq16413 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16280 eq111
    | exact resolve eq111 eq16280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16431 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq16413
  have eq16445 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16431
       have r₂ := eq16275
       grind)
    | exact resolve eq16431 eq16275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16431
  have eq16455 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq16445
  have eq16530 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq16455
    | exact resolve eq16455 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16455
  have eq16811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16530 eq111
    | exact resolve eq111 eq16530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq16530
  have eq16825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq16811
  have eq16829 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16825
       have r₂ := eq28
       grind)
    | exact resolve eq16825 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16825
  have eq16838 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq16829
  have eq16915 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16838
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16838
    | exact resolve eq16838 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16838
  have eq17135 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq16915
       grind)
    | exact superpose eq16915 eq45
    | exact resolve eq45 eq16915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16915
  have eq17153 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq17135
    | exact resolve eq17135 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17135
  have eq17176 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17153 eq16280
    | exact resolve eq16280 eq17153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16280
  have eq17182 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17176
  have eq17190 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17182
       have r₂ := eq16275
       grind)
    | exact resolve eq17182 eq16275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16275 eq17182
  have eq17317 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17190
  have eq17395 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq17317
    | exact resolve eq17317 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17317
  have eq18180 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17395 eq17153
    | exact resolve eq17153 eq17395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17153 eq17395
  have eq18184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq18180
  have eq18192 : y = (M.op x y) := by
    first
    | (have r₁ := eq18184
       have r₂ := eq28
       grind)
    | exact resolve eq18184 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18184
  have eq18194 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq18192 eq21
    | exact resolve eq21 eq18192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq18199 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq18192 eq71
    | (have r₁ := eq71
       have r₂ := eq18192
       grind)
    | exact resolve eq71 eq18192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq18251 : y = (k x y) ∨ x = (M.op y y) := by grind
  clear eq18199
  have eq18303 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18194
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18194
    | exact resolve eq18194 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18194
  have eq18453 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq18303 eq27
    | exact resolve eq27 eq18303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq19576 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq18251
       grind)
    | exact superpose eq18251 eq45
    | exact resolve eq45 eq18251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19588 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq764 x y
       have i₂ := eq18251
       grind)
    | exact superpose eq18251 eq764
    | (have j0 := eq764 x y
       grind)
    | exact resolve eq764 eq18251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18251
  have eq19591 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq19588
  have eq19598 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19591
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19591
    | exact resolve eq19591 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19591
  have eq19608 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18303 eq19576
    | exact resolve eq19576 eq18303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19576
  have eq19610 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18303 eq19598
    | exact resolve eq19598 eq18303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19598
  have eq19620 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19608
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19608
    | exact resolve eq19608 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19608
  have eq19621 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19610
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19610
    | exact resolve eq19610 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19610
  have eq19628 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18303 eq19620
    | exact resolve eq19620 eq18303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19620
  have eq19629 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18453 eq19621
    | exact resolve eq19621 eq18453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19621
  have eq19631 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq19629
       have r₂ := eq28
       grind)
    | exact resolve eq19629 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19629
  have eq19633 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19631
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19631
    | exact resolve eq19631 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19631
  have eq19635 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18303 eq19633
    | exact resolve eq19633 eq18303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19633
  have eq19637 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19635
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19635
    | exact resolve eq19635 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19635
  have eq19696 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by grind
  clear eq19637
  have eq19778 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18453 eq19696
    | exact resolve eq19696 eq18453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19696
  have eq19995 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19778 eq19628
    | exact resolve eq19628 eq19778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19628 eq19778
  have eq19999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq19995
  have eq20001 : x = (M.op y y) := by
    first
    | (have r₁ := eq19999
       have r₂ := eq28
       grind)
    | exact resolve eq19999 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19999
  have eq20014 : ∀ X0 : G, x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq20001
       have i₂ := eq591 X0 y
       grind)
    | (have i₁ := eq20001
       have i₂ := eq591 y X0
       grind)
    | exact superpose eq591 eq20001
    | exact resolve eq20001 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq20023 : (M.op x y) = (k x y) := by grind
  have eq20062 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq674 y x
       have i₂ := eq20001
       grind)
    | exact superpose eq20001 eq674
    | exact resolve eq674 eq20001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq20001
  have eq20105 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq20023
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20023
    | exact resolve eq20023 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20023
  have eq20107 : y = (k x y) := by
    first
    | exact superpose eq18192 eq20105
    | exact resolve eq20105 eq18192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18192 eq20105
  have eq20549 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq20107
       grind)
    | exact superpose eq20107 eq45
    | exact resolve eq45 eq20107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq20561 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq764 x y
       have i₂ := eq20107
       grind)
    | exact superpose eq20107 eq764
    | (have j0 := eq764 x y
       grind)
    | exact resolve eq764 eq20107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq20107
  have eq20564 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq20561
  have eq20570 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq20564
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20564
    | exact resolve eq20564 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20564
  have eq20580 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq18303 eq20549
    | exact resolve eq20549 eq18303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20549
  have eq20581 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq18303 eq20570
    | exact resolve eq20570 eq18303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20570
  have eq20591 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq20580
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20580
    | exact resolve eq20580 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20580
  have eq20592 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq20581
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20581
    | exact resolve eq20581 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20581
  have eq20599 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq18303 eq20591
    | exact resolve eq20591 eq18303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18303 eq20591
  have eq20600 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq18453 eq20592
    | exact resolve eq20592 eq18453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20592
  have eq20602 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq20600
       have r₂ := eq28
       grind)
    | exact resolve eq20600 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20600
  have eq20604 : x = (σ x) := by
    first
    | (have i₁ := eq20602
       have i₂ := eq20014 (σ y)
       grind)
    | exact superpose eq20014 eq20602
    | exact resolve eq20602 eq20014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20014 eq20602
  have eq20606 : x = (σ x) := by
    first
    | (have i₁ := eq20604
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20604
    | exact resolve eq20604 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq20604
  have eq20690 : (M.op (σ x) (σ y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq20606 eq18453
    | exact resolve eq18453 eq20606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18453
  have eq21000 : (σ (M.op x y)) = (k x (σ (M.op x y))) := by
    first
    | exact superpose eq20606 eq20599
    | exact resolve eq20599 eq20606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20599 eq20606
  have eq21155 : (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | (have i₁ := eq21000
       have i₂ := eq20062 sF1
       grind)
    | exact superpose eq20062 eq21000
    | exact resolve eq21000 eq20062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20062 eq21000
  have eq21156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20690 eq21155
    | exact resolve eq21155 eq20690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20690 eq21155
  have eq21222 : False := by grind
  exact eq21222

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pxx_pyx_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq175 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
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
  have eq529 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq175 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq175 x (M.op X0 X0) X0
       have i₂ := eq529 (M.op X0 X0) x X2
       grind)
    | (have i₁ := eq175 (M.op X2 X2) (M.op X2 X2) X2
       have i₂ := eq529 X0 x (M.op (M.op X2 X2) (M.op X2 X2))
       grind)
    | exact superpose eq529 eq175
    | exact resolve eq175 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq529
  have eq594 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq560 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq560 X1 X0
       grind)
    | exact superpose eq560 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq560 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X2 X2)
       have r₂ := eq560 (M.op X2 X2) X2
       grind)
    | exact resolve eq13 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1513 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq594 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq1515 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 x x
       have i₂ := eq560 X0 x
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq560 X0 x
       grind)
    | exact superpose eq560 eq11
    | (have j0 := eq11 X0 (k X1 X1)
       grind)
    | exact resolve eq11 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1552 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq560
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1596 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq1600 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq1605 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1606 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1605 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605
  have eq1622 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1552 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq1638 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1515 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515
  have eq1788 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 (M.op X1 X1)) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq1513 X0 X1
       grind)
    | exact superpose eq1513 eq16
    | exact resolve eq16 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3275 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1606 X1
       have i₂ := eq1622 X1 X0
       grind)
    | exact superpose eq1622 eq1606
    | (have j0 := eq1606 X1
       have j1 := eq1622 X1 X1
       grind)
    | (have r₁ := eq1606 (M.op X1 X1)
       have r₂ := eq1622 (M.op X1 X1) X1
       grind)
    | exact resolve eq1606 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606 eq1622
  have eq3293 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3275 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3275
  have eq3496 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1638 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638
  have eq4519 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1596
       grind)
    | exact superpose eq1596 eq39
    | exact resolve eq39 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq4520 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq3293 x x
       grind)
    | (have r₁ := eq4519
       have r₂ := eq3293 y x
       grind)
    | (have r₁ := eq4519
       have r₂ := eq3293 x x
       grind)
    | exact resolve eq4519 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4519
  have eq4522 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4520
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4520
    | exact resolve eq4520 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4520
  have eq4524 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq4522
    | exact resolve eq4522 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4522
  have eq5608 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1600 eq4524
    | exact resolve eq4524 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600 eq4524
  have eq5615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq3293 x x
       grind)
    | (have r₁ := eq5608
       have r₂ := eq3293 x x
       grind)
    | (have r₁ := eq5608
       have r₂ := eq3293 (σ y) (σ x)
       grind)
    | (have r₁ := eq5608
       have r₂ := eq3293 (σ x) (σ x)
       grind)
    | exact resolve eq5608 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3293 eq5608
  have eq5619 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq5615
       have r₂ := eq27
       grind)
    | exact resolve eq5615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5615
  have eq5826 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq5619 eq560
    | exact resolve eq560 eq5619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5619
  have eq5961 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq560 x X0
       have i₂ := eq5826 X1
       grind)
    | exact superpose eq5826 eq560
    | (have j1 := eq5826 X1
       grind)
    | exact resolve eq560 eq5826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq5826
  have eq6181 : ∀ X0 X1 : G, (σ x) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq1513 (M.op X0 X0) X0
       have i₂ := eq5961 X1 (M.op X0 X0)
       grind)
    | (have i₁ := eq1513 (M.op X1 X1) X1
       have i₂ := eq5961 (M.op X1 X1) X1
       grind)
    | exact superpose eq5961 eq1513
    | (have j1 := eq5961 X1 X1
       grind)
    | exact resolve eq1513 eq5961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6227 : ∀ X1 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op X1 X1) = x := by
    intro X1
    first
    | exact superpose eq5961 eq6181
    | (have j0 := eq6181 x X1
       have j1 := eq5961 X1 X1
       grind)
    | exact resolve eq6181 eq5961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5961 eq6181
  have eq6382 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) x) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq6227 eq141
    | (have j1 := eq6227 X0
       grind)
    | exact resolve eq141 eq6227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq6227
  have eq6389 : ∀ X0 : G, x = (k x x) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq29 eq6382
    | (have j0 := eq6382 X0
       grind)
    | exact resolve eq6382 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6382
  have eq6392 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq6389 X0
       have j1 := eq3496 X0 x
       grind)
    | (have r₁ := eq6389 X0
       have r₂ := eq3496 X0 x
       grind)
    | exact resolve eq6389 eq3496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6389
  have eq6491 : ∀ X0 : G, x = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1513 (M.op X0 X0) X0
       have i₂ := eq6392 (M.op X0 X0)
       grind)
    | exact superpose eq6392 eq1513
    | exact resolve eq1513 eq6392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq6536 : x = (k x x) := by
    first
    | (have i₁ := eq6491 x
       have i₂ := eq6392 x
       grind)
    | exact superpose eq6392 eq6491
    | exact resolve eq6491 eq6392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6491
  have eq6714 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq6536
       grind)
    | exact superpose eq6536 eq39
    | exact resolve eq39 eq6536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq6536
  have eq6721 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6714
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6714
    | exact resolve eq6714 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6714
  have eq6735 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq6721 eq3496
    | (have j0 := eq3496 X0 (σ x)
       grind)
    | (have r₁ := eq3496 X0 (σ x)
       have r₂ := eq6721
       grind)
    | exact resolve eq3496 eq6721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3496 eq6721
  have eq6736 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq6735 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6735
  have eq6832 : x = (σ x) := by
    first
    | (have i₁ := eq6392 x
       have i₂ := eq6736 x
       grind)
    | exact superpose eq6736 eq6392
    | exact resolve eq6392 eq6736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6870 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1788 X0 X1 (k X0 (M.op X1 X1))
       have i₂ := eq6736 (k X0 (M.op X1 X1))
       grind)
    | exact superpose eq6736 eq1788
    | exact resolve eq1788 eq6736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788 eq6736
  have eq6874 : ∀ X0 : G, (k X0 x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq6870 X0 x
       have i₂ := eq6392 x
       grind)
    | exact superpose eq6392 eq6870
    | exact resolve eq6870 eq6392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6392 eq6870
  have eq6965 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq6874 X0
       have i₂ := eq6832
       grind)
    | exact superpose eq6832 eq6874
    | exact resolve eq6874 eq6832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6874
  have eq7196 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6832
       grind)
    | exact superpose eq6832 eq18
    | exact resolve eq18 eq6832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7197 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq22
       have i₂ := eq6832
       grind)
    | exact superpose eq6832 eq22
    | exact resolve eq22 eq6832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6832
  have eq7217 : (M.op x y) = (k y (σ x)) := by
    first
    | exact superpose eq6965 eq7196
    | exact resolve eq7196 eq6965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7196
  have eq7444 : (σ (M.op x y)) = (k (σ y) (σ (σ x))) := by
    first
    | exact superpose eq7217 eq36
    | exact resolve eq36 eq7217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq7217
  have eq7447 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq7197 eq7444
    | exact resolve eq7444 eq7197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7197 eq7444
  have eq7448 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq7447
    | exact resolve eq7447 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq7447
  have eq10134 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq6965 eq26
    | (have j1 := eq6965 (σ y)
       grind)
    | exact resolve eq26 eq6965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6965
  have eq10275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7448 eq10134
    | exact resolve eq10134 eq7448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7448 eq10134
  have eq10346 : False := by grind
  exact eq10346

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pxy_pyx_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
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
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq63 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq63 x (M.op X0 X0) X0
       have i₂ := eq67 (M.op X0 X0) x X2
       grind)
    | (have i₁ := eq63 (M.op X2 X2) (M.op X2 X2) X2
       have i₂ := eq67 X0 x (M.op (M.op X2 X2) (M.op X2 X2))
       grind)
    | exact superpose eq67 eq63
    | exact resolve eq63 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq67
  have eq928 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1556 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 (σ X1)) = (σ (M.op X1 (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq928 X1 X2
       have i₂ := eq93 X0 X1
       grind)
    | (have i₁ := eq928 X1 X2
       have i₂ := eq93 X1 X0
       grind)
    | exact superpose eq93 eq928
    | (have j0 := eq928 X1 X2
       grind)
    | (have r₁ := eq928 (M.op X0 X0) X1
       have r₂ := eq93 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq928 (M.op X2 X2) X1
       have r₂ := eq93 (M.op X2 X2) X2
       grind)
    | exact resolve eq928 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1733 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq1740 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1733 X0 X1
       have j1 := eq1556 X0 X0 X1
       grind)
    | (have r₁ := eq1733 X1 X1
       have r₂ := eq1556 (τ X1) X1 x
       grind)
    | (have r₁ := eq1733 (M.op X0 X0) X1
       have r₂ := eq1556 X0 (M.op (τ X1) (τ X1)) x
       grind)
    | (have r₁ := eq1733 X1 X1
       have r₂ := eq1556 X1 X1 x
       grind)
    | exact resolve eq1733 eq1556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556 eq1733
  have eq1757 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1740 X0 X1
       have j1 := eq928 X0 X1
       grind)
    | (have r₁ := eq1740 X0 X1
       have r₂ := eq928 X0 X1
       grind)
    | exact resolve eq1740 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq1740
  have eq1758 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1757 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1757
    | exact resolve eq1757 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq5527 : ∀ X0 X1 : G, (τ (σ (M.op X0 X1))) = (k (τ (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq1758 X1 X0
       grind)
    | exact superpose eq1758 eq23
    | exact resolve eq23 eq1758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq5569 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5527 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5527
    | exact resolve eq5527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5527
  have eq5600 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5569 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq5569
    | exact resolve eq5569 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5569
  have eq5682 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1758 X1 X0
       have i₂ := eq5600 (σ X0) (σ X1)
       grind)
    | exact superpose eq5600 eq1758
    | exact resolve eq1758 eq5600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758 eq5600
  have eq6385 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5682 x y
       grind)
    | exact superpose eq5682 eq16
    | (have r₁ := eq16
       have r₂ := eq5682 x y
       grind)
    | exact resolve eq16 eq5682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5682
  have eq6450 : False := by grind
  exact eq6450
