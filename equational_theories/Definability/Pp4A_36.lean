import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
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
  have eq40 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq43 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 (k X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq36 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq41 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq41 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq41 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq42 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq42 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq25 X1
       grind)
    | exact superpose eq25 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq25 X1
       grind)
    | exact superpose eq25 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq48
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq43 X1 X0
       grind)
    | (have r₁ := eq52 X1 X0
       have r₂ := eq43 X0 X1
       grind)
    | (have r₁ := eq52 X0 (M.op X1 X1)
       have r₂ := eq43 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq52 X1 X1
       have r₂ := eq43 (k X1 X1) X1
       grind)
    | exact resolve eq52 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq52
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       have j1 := eq56 X0 X1
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq56 X0 X1
       grind)
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq109 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq113 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       have j1 := eq61 X1 X0
       grind)
    | (have r₁ := eq109 X1 X0
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq109 X0 X0
       have r₂ := eq61 X0 X0
       grind)
    | exact resolve eq109 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq109
  have eq261 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq113 (σ X1) (σ X0)
       grind)
    | exact superpose eq113 eq15
    | exact resolve eq15 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq261 X0 X1
       have i₂ := eq113 X1 X0
       grind)
    | exact superpose eq113 eq261
    | exact resolve eq261 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq261
  have eq269 : False := by grind
  exact eq269

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_x_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq51 : x ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
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
  have eq58 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
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
  have eq60 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
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
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X1)) X2) ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 (M.op X2 X1)) X2) (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq14 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  have eq77 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq84 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq77
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq124 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq147 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq269 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 (τ X1) X0
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq500 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq60 (M.op X0 X0) x x X3
       have i₂ := eq59 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq59 eq60
    | exact resolve eq60 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq582 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq708
    | exact resolve eq708 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq712 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq709
       have r₂ := eq28
       grind)
    | exact resolve eq709 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq714 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq712
    | exact resolve eq712 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq731 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ X2 ∨ (k X2 (M.op X0 (M.op (M.op X1 X1) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X0 (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X1))
       have i₂ := eq59 X0 X1 (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X1))
       grind)
    | exact superpose eq59 eq61
    | (have r₁ := eq61 (M.op X1 (M.op (M.op X0 X0) X1)) (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X1))
       have r₂ := eq59 X0 X1 (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X1))
       grind)
    | (have r₁ := eq61 (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       have r₂ := eq59 X0 X1 X2 (M.op (M.op X1 (M.op X2 X1)) X2)
       grind)
    | exact resolve eq61 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq732 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X1) = (k (M.op (M.op X0 (M.op X1 X0)) X1) (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq61 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq733 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (k X2 (M.op X0 (M.op (M.op X1 X1) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq731 X0 X1 X2
       have i₂ := eq500 X1 X0
       grind)
    | (have i₁ := eq731 X0 X1 X2
       have i₂ := eq500 X0 (M.op (M.op X1 X1) X0)
       grind)
    | exact superpose eq500 eq731
    | (have j0 := eq731 X0 X1 X2
       grind)
    | (have r₁ := eq731 (M.op X0 X0) X1 (M.op (M.op X1 X1) (M.op X0 X0))
       have r₂ := eq500 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq731 X0 X1 (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X1 X1) X0)))
       have r₂ := eq500 X0 (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact resolve eq731 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq741 : ∀ X0 X2 : G, (M.op X0 X0) ≠ X2 ∨ (k X2 (M.op X0 X0)) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq733 X0 x X2
       have i₂ := eq500 x X0
       grind)
    | (have i₁ := eq733 X0 x X2
       have i₂ := eq500 X0 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq500 eq733
    | (have j0 := eq733 X0 x X2
       grind)
    | (have r₁ := eq733 (M.op X0 X0) x (M.op X0 X0)
       have r₂ := eq500 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq733 X0 x (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq500 X0 (M.op X0 X0)
       grind)
    | exact resolve eq733 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq752 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq714 eq52
    | (have r₁ := eq52
       have r₂ := eq714
       grind)
    | exact resolve eq52 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq714
  have eq754 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq752
  have eq816 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq754 eq98
    | exact resolve eq98 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq817 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq754 eq84
    | exact resolve eq84 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq754
  have eq820 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq816
  have eq824 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq817
    | exact resolve eq817 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq827 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq824
       have r₂ := eq51
       grind)
    | exact resolve eq824 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq824
  have eq830 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq827
       grind)
    | exact superpose eq827 eq77
    | exact resolve eq77 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq827
  have eq835 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq830
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq830
    | exact resolve eq830 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq843 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq835 eq11
    | (have j0 := eq11 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq844 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq843
  have eq848 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq844
    | exact resolve eq844 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq851 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq848
    | exact resolve eq848 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq854 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq820 eq30
    | exact resolve eq30 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq873 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq854
    | exact resolve eq854 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq874 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq873
  have eq876 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq874 eq27
    | exact resolve eq27 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq877 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq874 eq30
    | exact resolve eq30 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq900 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq877
    | exact resolve eq877 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq904 : ∀ X0 : G, (M.op (M.op (M.op y y) x) X0) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq900 eq57
    | exact resolve eq57 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq900
  have eq920 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq904 X0
       have i₂ := eq500 y x
       grind)
    | (have i₁ := eq904 X0
       have i₂ := eq500 X0 (M.op (M.op y y) x)
       grind)
    | exact superpose eq500 eq904
    | exact resolve eq904 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq949 : ∀ X0 : G, x ≠ X0 ∨ (k X0 x) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq920 X0
       grind)
    | exact superpose eq920 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq920 x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq920 X0
       grind)
    | exact resolve eq13 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq1108 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ y)) (σ x)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq851 eq58
    | exact resolve eq58 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq851
  have eq1113 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1108 X0
       have i₂ := eq500 sF3 sF2
       grind)
    | (have i₁ := eq1108 X0
       have i₂ := eq500 X0 (M.op (M.op sF3 sF3) sF2)
       grind)
    | exact superpose eq500 eq1108
    | exact resolve eq1108 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq2248 : x = (k x x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have j0 := eq949 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq2250 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq2248
       grind)
    | exact superpose eq2248 eq44
    | exact resolve eq44 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2248
  have eq2254 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2250
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2250
    | exact resolve eq2250 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2250
  have eq2257 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2254
  have eq2258 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2257
  have eq2369 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2258 eq500
    | exact resolve eq500 eq2258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2258
  have eq2380 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2369 eq876
    | exact resolve eq876 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq2369
  have eq2397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2380
  have eq2407 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq2397
       have r₂ := eq28
       grind)
    | exact resolve eq2397 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397
  have eq2514 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2407 eq21
    | exact resolve eq21 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2544 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2514
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2514
    | exact resolve eq2514 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2514
  have eq2565 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq2544 eq1113
    | exact resolve eq1113 eq2544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113 eq2544
  have eq2574 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq2565 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2565
  have eq2585 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq2574 X0
       grind)
    | (have r₁ := eq2574 X0
       have r₂ := eq28
       grind)
    | exact resolve eq2574 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574
  have eq2814 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq582 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq582
    | (have j0 := eq582 (τ X0)
       grind)
    | exact resolve eq582 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq2823 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2814 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2814
    | (have j0 := eq2814 X0
       grind)
    | exact resolve eq2814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2814
  have eq2829 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2823 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2823
    | (have j0 := eq2823 X0
       grind)
    | exact resolve eq2823 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2823
  have eq8766 : ∀ X0 : G, (M.op (M.op X0 X0) (σ (M.op x y))) = (k (M.op (M.op X0 X0) (σ (M.op x y))) (M.op (M.op X0 X0) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2585 eq732
    | exact resolve eq732 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2585
  have eq8810 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8766 x
       have i₂ := eq500 x sF1
       grind)
    | (have i₁ := eq8766 x
       have i₂ := eq500 x (M.op (M.op x x) sF1)
       grind)
    | exact superpose eq500 eq8766
    | exact resolve eq8766 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8766
  have eq8829 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8810 eq147
    | exact resolve eq147 eq8810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq8810
  have eq8837 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31 eq8829
    | exact resolve eq8829 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8829
  have eq8866 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq8837
  have eq8867 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq8866
  have eq9176 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq8867 eq500
    | exact resolve eq500 eq8867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8867
  have eq10895 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq2407 eq9176
    | exact resolve eq9176 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9176
  have eq10940 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq10895 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10895
  have eq14273 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10940 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10940
    | (have j0 := eq10940 y
       grind)
    | exact resolve eq10940 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10940
  have eq14364 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq14273 eq30
    | exact resolve eq30 eq14273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14273
  have eq14415 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq14364
    | exact resolve eq14364 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14364
  have eq14416 : y = (M.op x y) ∨ x = y := by grind
  clear eq14415
  have eq14439 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14416 eq2407
    | exact resolve eq2407 eq14416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2407 eq14416
  have eq14526 : x = y := by grind
  clear eq14439
  have eq14563 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq14526
       grind)
    | exact superpose eq14526 eq19
    | exact resolve eq19 eq14526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq14564 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq14526
       grind)
    | exact superpose eq14526 eq25
    | exact resolve eq25 eq14526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq14526
  have eq14594 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14564
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14564
    | exact resolve eq14564 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14564
  have eq14597 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14594 eq27
    | exact resolve eq27 eq14594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14594
  have eq14696 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq500 x X0
       have i₂ := eq14563
       grind)
    | exact superpose eq14563 eq500
    | exact resolve eq500 eq14563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14722 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq14597 eq741
    | (have r₁ := eq741 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq14597
       grind)
    | exact resolve eq741 eq14597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq14723 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq14597 eq500
    | exact resolve eq500 eq14597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14756 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x y)) = (k (M.op (M.op X0 X0) (M.op x y)) (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq14696 eq732
    | exact resolve eq732 eq14696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732 eq14696
  have eq14809 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq14756 x
       have i₂ := eq500 x sF0
       grind)
    | (have i₁ := eq14756 x
       have i₂ := eq500 x (M.op (M.op x x) sF0)
       grind)
    | exact superpose eq500 eq14756
    | exact resolve eq14756 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq14756
  have eq14879 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ x) (σ y)))) ∨ (τ X0) = (M.op (σ x) (σ y)) ∨ (τ X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14723 eq269
    | (have j0 := eq269 (M.op (σ x) (σ y)) X0
       grind)
    | exact resolve eq269 eq14723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq14723
  have eq14880 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ x) (σ y)))) ∨ (τ X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14879 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14879
  have eq14881 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (σ y)))) = X0 ∨ (τ X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14880 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq14880
    | (have j0 := eq14880 X0
       grind)
    | exact resolve eq14880 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14880
  have eq14954 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14809 eq582
    | (have j0 := eq582 (M.op x y)
       grind)
    | exact resolve eq582 eq14809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq14809
  have eq14958 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq14954
  have eq14962 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq14958
    | exact resolve eq14958 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14958
  have eq19101 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (σ x) (σ y))))) ∨ (τ (σ X0)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14881 eq330
    | (have j1 := eq14881 (σ X0)
       grind)
    | exact resolve eq330 eq14881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14881
  have eq19106 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (σ x) (σ y))) ∨ (τ (σ X0)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19101 X0
       have i₂ := eq16 sF4
       grind)
    | exact superpose eq16 eq19101
    | (have j0 := eq19101 X0
       grind)
    | exact resolve eq19101 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19101
  have eq19135 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (τ (σ X0)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19106 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq19106
    | (have j0 := eq19106 X0
       grind)
    | exact resolve eq19106 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19106
  have eq19148 : ∀ X0 : G, (M.op (σ x) (σ y)) = X0 ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq19135 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq19135
    | (have j0 := eq19135 X0
       grind)
    | exact resolve eq19135 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19135
  have eq19156 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq19148 X0
       have j1 := eq14722 X0
       grind)
    | (have r₁ := eq19148 X0
       have r₂ := eq14722 X0
       grind)
    | (have r₁ := eq19148 (M.op (σ x) (σ y))
       have r₂ := eq14722 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq19148 (M.op (σ x) (σ y))
       have r₂ := eq14722 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq19148 eq14722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14722 eq19148
  have eq19207 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq19156 eq330
    | exact resolve eq330 eq19156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq19156
  have eq19212 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq19207 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq19207
    | exact resolve eq19207 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19207
  have eq19278 : (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq19212 eq2829
    | (have j0 := eq2829 (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq2829 (τ (M.op (σ x) (σ y)))
       have r₂ := eq19212 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq2829 eq19212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2829 eq19212
  have eq19307 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by grind
  clear eq19278
  have eq21314 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq14563
       grind)
    | exact superpose eq14563 eq70
    | exact resolve eq70 eq14563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq21315 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq21314
    | exact resolve eq21314 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21314
  have eq21316 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21315
       have i₂ := eq14563
       grind)
    | exact superpose eq14563 eq21315
    | exact resolve eq21315 eq14563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21315
  have eq21343 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq21316
  have eq21356 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14597 eq21343
    | exact resolve eq21343 eq14597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21343
  have eq21362 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21356
       have r₂ := eq28
       grind)
    | exact resolve eq21356 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21356
  have eq21365 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14597 eq21362
    | exact resolve eq21362 eq14597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21362
  have eq21391 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21365 eq19307
    | exact resolve eq19307 eq21365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19307 eq21365
  have eq21406 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq21391
    | exact resolve eq21391 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21391
  have eq21415 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21406
       have i₂ := eq14563
       grind)
    | exact superpose eq14563 eq21406
    | exact resolve eq21406 eq14563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14563 eq21406
  have eq21416 : x = (M.op x y) := by grind
  clear eq21415
  have eq21428 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21416 eq21
    | exact resolve eq21 eq21416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq21416
  have eq21520 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21428
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21428
    | exact resolve eq21428 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21428
  have eq21599 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21520 eq14597
    | exact resolve eq14597 eq21520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14597 eq21520
  have eq21605 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14962 eq21599
    | exact resolve eq21599 eq14962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14962 eq21599
  have eq21623 : False := by grind
  exact eq21623

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq180 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1012 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1104 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1104 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1104 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq1104 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq1104 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq1104 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1154 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq1105 X0
       grind)
    | exact superpose eq1105 eq180
    | exact resolve eq180 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1510 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq40
    | exact resolve eq40 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1511 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1510
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1510
    | exact resolve eq1510 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510
  have eq1513 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq1511
    | exact resolve eq1511 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq1521 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1513 eq1013
    | exact resolve eq1013 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1528 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1521
       have r₂ := eq27
       grind)
    | exact resolve eq1521 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq1533 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1528 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1528
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1528
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1528
       grind)
    | exact resolve eq12 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528
  have eq1538 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1533
       have r₂ := eq26
       grind)
    | exact resolve eq1533 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq1541 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1538
       have i₂ := eq1105 sF2
       grind)
    | exact superpose eq1105 eq1538
    | exact resolve eq1538 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1543 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1513 eq1541
    | exact resolve eq1541 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513 eq1541
  have eq1544 : (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1543
       have r₂ := eq27
       grind)
    | exact resolve eq1543 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1545 : (τ (σ y)) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1544 eq98
    | exact resolve eq98 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1557 : (M.op x y) = (M.op y x) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq1545
    | exact resolve eq1545 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545
  have eq1572 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1557
       grind)
    | exact superpose eq1557 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1557
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1557
       grind)
    | exact resolve eq12 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557
  have eq1577 : y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (k x x) := by
    first
    | (have r₁ := eq1572
       have r₂ := eq18
       grind)
    | exact resolve eq1572 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq1580 : y = (k x x) ∨ (M.op x y) = (k y x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1577
       have i₂ := eq1105 x
       grind)
    | exact superpose eq1105 eq1577
    | exact resolve eq1577 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1577
  have eq1581 : (M.op x y) = (k y x) ∨ y = (k x x) := by grind
  clear eq1580
  have eq1596 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1581
       grind)
    | exact superpose eq1581 eq40
    | exact resolve eq40 eq1581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq1597 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1596
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1596
    | exact resolve eq1596 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1599 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq20 eq1597
    | exact resolve eq1597 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597
  have eq1602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq1599 eq1013
    | exact resolve eq1013 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1609 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq1602
       have r₂ := eq27
       grind)
    | exact resolve eq1602 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602
  have eq1614 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq1609 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1609
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1609
       grind)
    | exact resolve eq12 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609
  have eq1619 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq1614
       have r₂ := eq26
       grind)
    | exact resolve eq1614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614
  have eq1622 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1619
       have i₂ := eq1105 sF2
       grind)
    | exact superpose eq1105 eq1619
    | exact resolve eq1619 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105 eq1619
  have eq1624 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq1599 eq1622
    | exact resolve eq1622 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599 eq1622
  have eq1625 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq1624
       have r₂ := eq27
       grind)
    | exact resolve eq1624 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624
  have eq1626 : (τ (σ y)) = (k x x) ∨ y = (k x x) := by
    first
    | exact superpose eq1625 eq98
    | exact resolve eq98 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq1625
  have eq1638 : y = (k x x) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq1626
    | exact resolve eq1626 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1626
  have eq1639 : y = (k x x) := by grind
  clear eq1638
  have eq1645 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1639
       grind)
    | exact superpose eq1639 eq40
    | exact resolve eq40 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1653 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1645
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1645
    | exact resolve eq1645 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1645
  have eq1655 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1653
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1653
    | exact resolve eq1653 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq10135 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1154 x
       have i₂ := eq1639
       grind)
    | exact superpose eq1639 eq1154
    | exact resolve eq1154 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639
  have eq10137 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1655 eq1154
    | exact resolve eq1154 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154 eq1655
  have eq10352 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq10137
    | exact resolve eq10137 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq10137
  have eq10353 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq10135
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10135
    | exact resolve eq10135 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10135
  have eq10464 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq10353
       grind)
    | exact superpose eq10353 eq40
    | exact resolve eq40 eq10353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq10353
  have eq10466 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10464
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10464
    | exact resolve eq10464 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10464
  have eq10469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10352 eq10466
    | exact resolve eq10466 eq10352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10352 eq10466
  have eq10471 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10469
    | exact resolve eq10469 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10469
  have eq10473 : False := by grind
  exact eq10473

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pyy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
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
  have eq76 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq76 y x
       grind)
    | exact superpose eq76 eq73
    | (have j1 := eq76 y x
       grind)
    | exact resolve eq73 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq107
    | exact resolve eq107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq129 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq38
  have eq209 : ∀ X0 : G, (M.op (M.op y (M.op x y)) x) ≠ (M.op (M.op y (M.op x y)) x) ∨ (M.op (M.op (M.op y (M.op x y)) x) X0) = (k X0 (M.op (M.op y (M.op x y)) x)) := by
    intro X0
    first
    | exact superpose eq51 eq13
    | (have j0 := eq13 X0 (M.op (M.op y (M.op x y)) x)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op y (M.op x y)) x)
       have r₂ := eq51 (M.op (M.op y (M.op x y)) x)
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = (k X0 (M.op (M.op y (M.op x y)) x)) := by
    intro X0
    first
    | (have j0 := eq209 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq211 : ∀ X0 : G, (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq210
    | exact resolve eq210 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq210
  have eq215 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ≠ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) := by
    intro X0
    first
    | exact superpose eq52 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       have r₂ := eq52 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       grind)
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) := by
    intro X0
    first
    | (have j0 := eq215 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq217 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq52 eq216
    | exact resolve eq216 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq216
  have eq571 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
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
  clear eq53 eq54
  have eq888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq108 eq76
    | (have j0 := eq76 (σ y) (σ x)
       grind)
    | exact resolve eq76 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq888
    | exact resolve eq888 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq892 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq889
       have r₂ := eq28
       grind)
    | exact resolve eq889 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq901 : ∀ X0 : G, x = (M.op y y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq892 eq571
    | exact resolve eq571 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq919 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq571 y X0
       have i₂ := eq901 X1
       grind)
    | exact superpose eq901 eq571
    | (have j1 := eq901 X1
       grind)
    | exact resolve eq571 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq960 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq919
    | (have j0 := eq919 X0 (σ y)
       grind)
    | exact resolve eq919 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq990 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq960 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq960
    | (have j0 := eq960 y
       grind)
    | exact resolve eq960 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq1020 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (σ y)) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq990 eq217
    | exact resolve eq217 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1022 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq990 eq28
    | exact resolve eq28 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1024 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1020 X0
       have i₂ := eq571 sF3 sF2
       grind)
    | (have i₁ := eq1020 X0
       have i₂ := eq571 X0 (M.op (M.op sF3 sF3) sF2)
       grind)
    | exact superpose eq571 eq1020
    | exact resolve eq1020 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1095 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1024 eq108
    | exact resolve eq108 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1024
  have eq1103 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1095
       have r₂ := eq1022
       grind)
    | exact resolve eq1095 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022 eq1095
  have eq1252 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq571 y X0
       have i₂ := eq1103
       grind)
    | exact superpose eq1103 eq571
    | exact resolve eq571 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1331 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1252 y
       grind)
    | exact superpose eq1252 eq19
    | (have j1 := eq1252 y
       grind)
    | exact resolve eq19 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1252
  have eq1355 : y = (M.op x y) := by grind
  clear eq1331
  have eq1370 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1355 eq21
    | exact resolve eq21 eq1355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1379 : ∀ X0 : G, (k X0 (M.op (M.op y y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq1355 eq211
    | exact resolve eq211 eq1355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq1355
  have eq1384 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq1379 X0
       have i₂ := eq571 y x
       grind)
    | (have i₁ := eq1379 X0
       have i₂ := eq571 X0 (M.op (M.op y y) x)
       grind)
    | exact superpose eq571 eq1379
    | exact resolve eq1379 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq1393 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1370
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1370
    | exact resolve eq1370 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1370
  have eq1395 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1393 eq27
    | exact resolve eq27 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1393
  have eq1424 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq1384 sF0
       grind)
    | exact superpose eq1384 eq129
    | exact resolve eq129 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1384
  have eq1430 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq21 eq1424
    | exact resolve eq1424 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1424
  have eq1489 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1430 eq76
    | (have j0 := eq76 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq76 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1430
  have eq1490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1395 eq1489
    | exact resolve eq1489 eq1395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq1493 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1490
       have r₂ := eq28
       grind)
    | exact resolve eq1490 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq1565 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1493 eq571
    | exact resolve eq571 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq1493
  have eq1607 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1565 eq1395
    | exact resolve eq1395 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395 eq1565
  have eq1648 : False := by grind
  exact eq1648

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyx_pxy_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
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
  have eq530 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
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
  have eq534 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
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
  have eq561 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq176 x (M.op X0 X0) X0
       have i₂ := eq530 (M.op X0 X0) x X2
       grind)
    | (have i₁ := eq176 (M.op X2 X2) (M.op X2 X2) X2
       have i₂ := eq530 X0 x (M.op (M.op X2 X2) (M.op X2 X2))
       grind)
    | exact superpose eq530 eq176
    | exact resolve eq176 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq713 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq534 X0 X1 x
       grind)
    | exact superpose eq534 eq16
    | exact resolve eq16 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq798 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq713 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq713
    | (have j0 := eq713 x X0 y
       grind)
    | exact resolve eq713 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq26 eq713
    | (have j0 := eq713 (σ x) X0 (σ y)
       grind)
    | exact resolve eq713 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq1530 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1533 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28
  have eq1682 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1686 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1682 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1682 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1682 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682
  have eq1777 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X1 X2 X0
       have i₂ := eq1686 X0
       grind)
    | exact superpose eq1686 eq176
    | exact resolve eq176 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1789 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq561 X0 X1
       have i₂ := eq1686 X0
       grind)
    | exact superpose eq1686 eq561
    | exact resolve eq561 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq1797 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq798 X0
       have i₂ := eq1686 X0
       grind)
    | exact superpose eq1686 eq798
    | exact resolve eq798 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq1798 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq799 X0
       have i₂ := eq1686 X0
       grind)
    | exact superpose eq1686 eq799
    | exact resolve eq799 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq1870 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) (M.op X2 (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1777 X0 X1 X2
       have i₂ := eq1686 X1
       grind)
    | exact superpose eq1686 eq1777
    | exact resolve eq1777 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq1973 : ∀ X0 X1 : G, (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1686 X0
       have i₂ := eq1789 X1 X0
       grind)
    | exact superpose eq1789 eq1686
    | exact resolve eq1686 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789
  have eq3874 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1530
       grind)
    | exact superpose eq1530 eq41
    | exact resolve eq41 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq3875 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3874
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3874
    | exact resolve eq3874 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3874
  have eq3877 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq3875
    | exact resolve eq3875 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3875
  have eq3879 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq3877
       have i₂ := eq1686 y
       grind)
    | exact superpose eq1686 eq3877
    | exact resolve eq3877 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3877
  have eq3890 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq3879 eq1533
    | exact resolve eq1533 eq3879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3879
  have eq3897 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k y y) := by
    first
    | (have r₁ := eq3890
       have r₂ := eq27
       grind)
    | exact resolve eq3890 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3890
  have eq3901 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq3897
       have i₂ := eq1686 sF3
       grind)
    | exact superpose eq1686 eq3897
    | exact resolve eq3897 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3897
  have eq3909 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq3901 eq1798
    | exact resolve eq1798 eq3901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798
  have eq3913 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ (M.op x y) = (k y y) := by
    intro X0
    first
    | exact superpose eq3901 eq1973
    | exact resolve eq1973 eq3901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9543 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 (M.op (σ x) (σ y)))) = X1 ∨ (M.op x y) = (k y y) := by
    intro X0 X1
    first
    | exact superpose eq3901 eq1870
    | exact resolve eq1870 eq3901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3901
  have eq9602 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (σ y)))) = X1 ∨ (M.op x y) = (k y y) := by
    intro X1
    first
    | exact superpose eq3913 eq9543
    | exact resolve eq9543 eq3913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3913 eq9543
  have eq12491 : (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq9602 eq3909
    | exact resolve eq3909 eq9602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3909 eq9602
  have eq12502 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq12491
  have eq12802 : y = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1797 y
       have i₂ := eq12502
       grind)
    | exact superpose eq12502 eq1797
    | exact resolve eq1797 eq12502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797
  have eq12807 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 (M.op x y))) = X1 ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq1870 y X0 X1
       have i₂ := eq12502
       grind)
    | exact superpose eq12502 eq1870
    | exact resolve eq1870 eq12502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1870
  have eq12811 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1973 y X0
       have i₂ := eq12502
       grind)
    | exact superpose eq12502 eq1973
    | exact resolve eq1973 eq12502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973 eq12502
  have eq12847 : ∀ X1 : G, (M.op (M.op x y) (M.op X1 (M.op x y))) = X1 ∨ (σ x) = (σ y) := by
    intro X1
    first
    | exact superpose eq12811 eq12807
    | exact resolve eq12807 eq12811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12807 eq12811
  have eq14433 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12847 eq12802
    | exact resolve eq12802 eq12847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12802 eq12847
  have eq14450 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq14433
  have eq14536 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq14450 eq32
    | exact resolve eq32 eq14450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq14450
  have eq14562 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq14536
    | exact resolve eq14536 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14536
  have eq14563 : x = y := by grind
  clear eq14562
  have eq14566 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq14563
       grind)
    | exact superpose eq14563 eq24
    | exact resolve eq24 eq14563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq14569 : (M.op x y) = (k x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1530
       have i₂ := eq14563
       grind)
    | exact superpose eq14563 eq1530
    | exact resolve eq1530 eq14563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530 eq14563
  have eq14593 : (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq14569
       have i₂ := eq1686 x
       grind)
    | exact superpose eq1686 eq14569
    | exact resolve eq14569 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14569
  have eq14594 : (M.op x y) = (k x x) := by grind
  clear eq14593
  have eq14597 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14566
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14566
    | exact resolve eq14566 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14566
  have eq14610 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14597 eq1533
    | exact resolve eq1533 eq14597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533 eq14597
  have eq14616 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq14610
       have i₂ := eq1686 sF2
       grind)
    | exact superpose eq1686 eq14610
    | exact resolve eq14610 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686 eq14610
  have eq14617 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq14616
  have eq14641 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq14594
       grind)
    | exact superpose eq14594 eq40
    | exact resolve eq40 eq14594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq14594
  have eq14705 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq14641
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14641
    | exact resolve eq14641 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq14641
  have eq14720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14617 eq14705
    | exact resolve eq14705 eq14617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14617 eq14705
  have eq14726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq14720
    | exact resolve eq14720 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq14720
  have eq14729 : False := by grind
  exact eq14729

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxx_pyx_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq41 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq39 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq39 X0 X1
       grind)
    | exact resolve eq44 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq44
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq52
  have eq84 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq20 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq137 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq905 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op X2 X3) ∨ (M.op X2 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X2 X3
       have i₂ := eq84 X1 X0 X2
       grind)
    | (have i₁ := eq55 (M.op X0 X0) X1
       have i₂ := eq84 X0 X0 X2
       grind)
    | exact superpose eq84 eq55
    | (have j0 := eq55 X2 X3
       grind)
    | exact resolve eq55 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1568 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ (M.op X2 X3) ∨ (M.op X2 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq137 X3 X2
       have i₂ := eq84 X1 X0 X3
       grind)
    | (have i₁ := eq137 (M.op X0 X0) X1
       have i₂ := eq84 X0 X0 X2
       grind)
    | exact superpose eq84 eq137
    | (have j0 := eq137 X3 X2
       grind)
    | (have r₁ := eq137 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq84 X0 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq137 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq84 X0 X1 (M.op X0 X0)
       grind)
    | exact resolve eq137 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq137
  have eq1596 : ∀ X2 X3 : G, (M.op X2 X3) = (k X3 X2) := by
    intro X2 X3
    first
    | (have j0 := eq1568 x x X2 X3
       have j1 := eq905 x x X2 X3
       grind)
    | (have r₁ := eq1568 x x X2 X3
       have r₂ := eq905 x x X2 X3
       grind)
    | (have r₁ := eq1568 x x (M.op x x) (M.op x x)
       have r₂ := eq905 x x (M.op x x) (M.op x x)
       grind)
    | exact resolve eq1568 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq1568
  have eq36665 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1596 (σ X0) (σ X1)
       grind)
    | exact superpose eq1596 eq15
    | exact resolve eq15 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36684 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36665 X0 X1
       have i₂ := eq1596 X0 X1
       grind)
    | exact superpose eq1596 eq36665
    | exact resolve eq36665 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596 eq36665
  have eq36709 : False := by grind
  exact eq36709

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyx_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (k (τ (σ X0)) X0) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq12 (τ (σ X0)) X0
       grind)
    | (have r₁ := eq12 (τ (σ X0)) X0
       have r₂ := eq10 X0
       grind)
    | (have r₁ := eq12 X0 (τ (σ X0))
       have r₂ := eq10 X0
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq17 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq15
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq37
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (τ X0)
       have i₂ := eq22 (τ X0)
       grind)
    | exact superpose eq22 eq28
    | exact resolve eq28 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq50 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq50
    | exact resolve eq50 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq50
  have eq60 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
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
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
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
  have eq114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq120 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq114
    | (have j0 := eq114 X0 X1
       grind)
    | exact resolve eq114 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq149 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (σ X0) X1 X2
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq61
    | exact resolve eq61 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq61 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq185 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq10
    | exact resolve eq10 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1640 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60 X0 X2 X3 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq60 X0 X1 X2 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq60
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1695 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1640 X0 X1 x x
       have i₂ := eq60 X0 x x X0
       grind)
    | exact superpose eq60 eq1640
    | (have j0 := eq1640 X0 X1 x x
       grind)
    | exact resolve eq1640 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1640
  have eq1696 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1695 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq3875 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq120 x y
       grind)
    | exact superpose eq120 eq16
    | (have j1 := eq120 x y
       grind)
    | exact resolve eq16 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq6025 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq164 X0 X1 x
       grind)
    | exact superpose eq164 eq9
    | exact resolve eq9 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq14762 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6025 X1 (τ X0) X2
       have i₂ := eq185 X0
       grind)
    | exact superpose eq185 eq6025
    | exact resolve eq6025 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6025
  have eq54666 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 X1)) (M.op X2 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq149 X1 X2 (τ X0)
       have i₂ := eq185 X0
       grind)
    | exact superpose eq185 eq149
    | exact resolve eq149 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq185
  have eq58930 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3875
       have i₂ := eq1696 x y
       grind)
    | exact superpose eq1696 eq3875
    | (have j1 := eq1696 (M.op (σ x) (σ y)) (σ (M.op x x))
       grind)
    | (have r₁ := eq3875
       have r₂ := eq1696 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3875
       have r₂ := eq1696 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3875 eq1696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696 eq3875
  have eq58932 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq58930
  have eq778358 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (τ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14762 X0 (σ x) (σ y)
       have i₂ := eq58932
       grind)
    | exact superpose eq58932 eq14762
    | exact resolve eq14762 eq58932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14762 eq58932
  have eq778376 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq778358 x
       have i₂ := eq54666 x x (σ x)
       grind)
    | exact superpose eq54666 eq778358
    | exact resolve eq778358 eq54666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54666 eq778358
  have eq778377 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq778376
  have eq778406 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq778377
       grind)
    | exact superpose eq778377 eq10
    | exact resolve eq10 eq778377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778377
  have eq778472 : x = y ∨ x = y := by
    first
    | (have i₁ := eq778406
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq778406
    | exact resolve eq778406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778406
  have eq778473 : x = y := by grind
  clear eq778472
  have eq779234 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq778473
       grind)
    | exact superpose eq778473 eq16
    | exact resolve eq16 eq778473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778473
  have eq779235 : False := by grind
  exact eq779235

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_x_pxx_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq19 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq21 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq23 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : (M.op x y) = (M.op x y) := by grind
  have eq25 : (M.op x y) = (M.op x y) := by grind
  clear eq24
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq27 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq26
  have eq28 : (σ x) = (σ x) := by grind
  have eq29 : (σ x) = (σ x) := by grind
  clear eq28
  have eq30 : (σ y) = (σ y) := by grind
  have eq31 : (σ y) = (σ y) := by grind
  clear eq30
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq33 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq32
  have eq34 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq35 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq19
    | (have j1 := eq20 X0
       grind)
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20
  have eq36 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq23 eq22
    | (have j1 := eq23 X0
       grind)
    | exact resolve eq22 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq29
       grind)
    | exact superpose eq29 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq41 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq31
       grind)
    | exact superpose eq31 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq44 : (M.op x y) = (M.op x (τ (σ y))) := by
    first
    | (have i₁ := eq25
       have i₂ := eq41
       grind)
    | exact superpose eq41 eq25
    | exact resolve eq25 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq41
  have eq45 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq44
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq44
    | exact resolve eq44 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq44
  have eq48 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
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
  have eq51 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (τ X0) X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq48
    | exact resolve eq48 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (M.op x y) X0
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 X0 (M.op x y)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq68 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq55 (τ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq55
    | exact resolve eq55 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq88 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq60
    | exact resolve eq60 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq105 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 ∨ (k X1 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 (M.op X2 X2)) X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq14
    | (have j0 := eq14 (M.op (M.op (M.op X1 (M.op X2 X2)) X0) (M.op (M.op X1 (M.op X2 X2)) X0)) X0
       grind)
    | exact resolve eq14 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq45 eq14
    | (have j0 := eq14 (M.op x y) (k (τ (σ y)) (τ (σ x)))
       grind)
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) X0) = (M.op (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X2 X2))) ∨ (M.op (k X0 (M.op X1 (M.op X2 X2))) X1) = X0 ∨ (M.op X1 (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 (M.op X1 (M.op X2 X2))
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (τ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq51
    | exact resolve eq51 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq168 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X2 X2)) (M.op X1 X1) X1
       have i₂ := eq50 (M.op X1 X1) X0 X2
       grind)
    | exact superpose eq50 eq9
    | exact resolve eq9 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq50 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       grind)
    | exact superpose eq50 eq9
    | exact resolve eq9 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq50 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq50 eq9
    | exact resolve eq9 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq108 eq34
    | exact resolve eq34 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq261 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X1 (M.op X2 X2)) X0))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op (M.op X1 (M.op X2 X2)) X0) X3 X4 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq49
    | exact resolve eq49 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 : G, (τ (σ y)) = (M.op (M.op x y) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (τ (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq45 eq49
    | exact resolve eq49 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq33 eq49
    | (have j0 := eq49 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq49 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X2)) X0) = (M.op X0 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X1 (M.op X2 X2)) X0))) ∨ (k X1 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op (M.op X1 (M.op X2 X2)) X0) X3 X4 (M.op (M.op X1 (M.op X2 X2)) X0)
       have i₂ := eq105 X0 X1 X2
       grind)
    | exact superpose eq105 eq49
    | (have j1 := eq105 X0 X1 X2
       grind)
    | exact resolve eq49 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq575 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) X0) = X1 ∨ (k X1 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq574 X0 X1 X2 x x
       have i₂ := eq261 X0 X1 X2 x x
       grind)
    | exact superpose eq261 eq574
    | (have j0 := eq574 X0 X1 X2 x x
       grind)
    | exact resolve eq574 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq576 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq575 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq580 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq106 eq15
    | exact resolve eq15 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq581 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq580
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq580
    | exact resolve eq580 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq582 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq581
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq581
    | exact resolve eq581 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq583 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq27 eq582
    | exact resolve eq582 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq599 : ∀ X0 X1 : G, (τ (σ x)) = (M.op (M.op x y) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq583 eq49
    | exact resolve eq49 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq600 : (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq264 eq599
    | exact resolve eq599 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq599
  have eq601 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq600
  have eq662 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op X0 (M.op X1 X1)) X2) (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op X0 (M.op X1 X1)))) ∨ (M.op (k X2 (M.op X0 (M.op X1 X1))) X0) = X2 ∨ (M.op X0 (M.op X1 X1)) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op X0 (M.op X1 X1)) X3 X4 (M.op X0 (M.op X1 X1))
       have i₂ := eq111 X2 X0 X1
       grind)
    | (have i₁ := eq49 (M.op X1 (M.op X2 X2)) X1 X2 X0
       have i₂ := eq111 X0 X1 X2
       grind)
    | exact superpose eq111 eq49
    | (have j1 := eq111 X2 X0 X1
       grind)
    | exact resolve eq49 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq666 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = X2 ∨ (M.op (k X2 (M.op X0 (M.op X1 X1))) X0) = X2 ∨ (M.op X0 (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq662 X0 X1 X2 x x
       have i₂ := eq49 (M.op X0 (M.op X1 X1)) x x X2
       grind)
    | exact superpose eq49 eq662
    | (have j0 := eq662 X0 X1 X2 x x
       grind)
    | exact resolve eq662 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq667 : ∀ X0 X1 X2 : G, (M.op (k X2 (M.op X0 (M.op X1 X1))) X0) = X2 ∨ (M.op X0 (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq666 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq685 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq601 eq224
    | (have r₁ := eq224
       have r₂ := eq601
       grind)
    | exact resolve eq224 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq601
  have eq686 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq685
  have eq838 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq686 eq49
    | exact resolve eq49 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq841 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq266 eq838
    | exact resolve eq838 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq838
  have eq842 : (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq841
  have eq844 : (σ y) = (σ (τ (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq842 eq36
    | exact resolve eq36 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq845 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq844
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq844
    | exact resolve eq844 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq846 : (σ x) = (σ y) := by grind
  clear eq845
  have eq999 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq846 eq45
    | exact resolve eq45 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq1000 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq846 eq33
    | exact resolve eq33 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq846
  have eq1007 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1000 eq50
    | exact resolve eq50 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1015 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1000 eq168
    | exact resolve eq168 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq1031 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1007 X0 x
       have i₂ := eq1015 X0 x
       grind)
    | exact superpose eq1015 eq1007
    | exact resolve eq1007 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1072 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (σ x) (σ y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1000 eq169
    | exact resolve eq169 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1133 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1072 X0 x
       have i₂ := eq1015 X0 x
       grind)
    | exact superpose eq1015 eq1072
    | exact resolve eq1072 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1209 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1031 eq50
    | exact resolve eq50 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1214 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq1031 eq169
    | exact resolve eq169 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1220 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1214 x
       have i₂ := eq1015 sF6 x
       grind)
    | exact superpose eq1015 eq1214
    | exact resolve eq1214 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1396 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1133 eq49
    | exact resolve eq49 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1399 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (M.op X1 X1) (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1396 X0 X1 x
       have i₂ := eq1015 (M.op X1 X1) x
       grind)
    | exact superpose eq1015 eq1396
    | exact resolve eq1396 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1405 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq1209 eq1399
    | exact resolve eq1399 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1408 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1031 eq1405
    | exact resolve eq1405 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq1675 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X1)) X0 X1
       have i₂ := eq1408 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq1408 eq9
    | exact resolve eq9 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1677 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq999
       have i₂ := eq1408 (τ sF4)
       grind)
    | exact superpose eq1408 eq999
    | exact resolve eq999 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1684 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | exact superpose eq1677 eq1675
    | exact resolve eq1675 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1675
  have eq1719 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq1684 X0 x
       have i₂ := eq1408 x
       grind)
    | exact superpose eq1408 eq1684
    | exact resolve eq1684 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1729 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1677 eq1719
    | exact resolve eq1719 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq1755 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq1677 eq1031
    | exact resolve eq1031 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1757 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1677 eq34
    | exact resolve eq34 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4914 : ∀ X0 X1 X2 : G, (M.op (k X1 X0) (M.op X0 (M.op X2 X2))) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq667 (M.op X0 (M.op X1 X1)) X2 X2
       have i₂ := eq169 X0 X1 X2
       grind)
    | exact superpose eq169 eq667
    | exact resolve eq667 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq4916 : ∀ X0 X1 X2 : G, (M.op (k X1 X0) (M.op (M.op X2 X2) X0)) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq667 (M.op (M.op X0 X0) X2) X1 X2
       have i₂ := eq170 X0 X1 X2
       grind)
    | exact superpose eq170 eq667
    | exact resolve eq667 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq4948 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op X1 X1))) ∨ (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1133 (k x (M.op sF6 (M.op X1 X1)))
       have i₂ := eq667 sF6 X1 x
       grind)
    | exact superpose eq667 eq1133
    | (have j1 := eq667 (M.op (σ x) (σ y)) X1 X0
       grind)
    | exact resolve eq1133 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq1133
  have eq4952 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4948 X0 X1
       have i₂ := eq1015 sF6 X1
       grind)
    | exact superpose eq1015 eq4948
    | (have j0 := eq4948 X0 X1
       grind)
    | exact resolve eq4948 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4948
  have eq4981 : ∀ X0 X1 : G, (M.op (k X1 X0) (M.op (M.op (σ x) (σ y)) X0)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4916 X0 X1 x
       have i₂ := eq1408 x
       grind)
    | exact superpose eq1408 eq4916
    | (have j0 := eq4916 (M.op (k X1 X0) (M.op (M.op (σ x) (σ y)) X0)) X1 x
       grind)
    | exact resolve eq4916 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4916
  have eq4982 : ∀ X0 X1 : G, (M.op (k X1 X0) (M.op X0 (M.op (σ x) (σ y)))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4914 X0 X1 x
       have i₂ := eq1015 X0 x
       grind)
    | exact superpose eq1015 eq4914
    | (have j0 := eq4914 (M.op (k X1 X0) (M.op X0 (M.op (σ x) (σ y)))) X1 x
       grind)
    | exact resolve eq4914 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4914
  have eq5005 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1220 eq4952
    | (have j0 := eq4952 X0 X1
       grind)
    | exact resolve eq4952 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4952
  have eq5034 : ∀ X0 X1 : G, (M.op (k X1 X0) (M.op (M.op x y) X0)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq1677 eq4981
    | (have j0 := eq4981 (M.op (k X1 X0) (M.op (M.op x y) X0)) X1
       grind)
    | exact resolve eq4981 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4981
  have eq5035 : ∀ X0 X1 : G, (M.op (k X1 X0) (M.op X0 (M.op x y))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq1677 eq4982
    | (have j0 := eq4982 (M.op (k X1 X0) (M.op X0 (M.op x y))) X1
       grind)
    | exact resolve eq4982 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4982
  have eq5058 : ∀ X0 X1 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1677 eq5005
    | (have j0 := eq5005 X0 X1
       grind)
    | exact resolve eq5005 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5005
  have eq5101 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = X0 ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq5058 X0 x
       have i₂ := eq1015 sF6 x
       grind)
    | exact superpose eq1015 eq5058
    | (have j0 := eq5058 X0 x
       grind)
    | exact resolve eq5058 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5058
  have eq5140 : ∀ X0 : G, (M.op (σ x) (σ y)) = X0 ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1220 eq5101
    | (have j0 := eq5101 X0
       grind)
    | exact resolve eq5101 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq5101
  have eq5179 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq1677 eq5140
    | (have j0 := eq5140 X0
       grind)
    | exact resolve eq5140 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5140
  have eq5703 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X1) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op X2 X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op X2 X2)))) X1 X2
       have i₂ := eq261 (M.op X1 (M.op X2 X2)) X0 X5 X3 X4
       grind)
    | exact superpose eq261 eq9
    | exact resolve eq9 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5718 : ∀ X0 X1 X3 X4 X5 : G, (M.op X0 X1) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq5703 X0 X1 x X3 X4 X5
       have i₂ := eq1015 X1 x
       grind)
    | exact superpose eq1015 eq5703
    | exact resolve eq5703 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5703
  have eq5843 : ∀ X0 X1 X3 X4 X5 : G, (M.op X0 X1) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op x y)))) := by
    intro X0 X1 X3 X4 X5
    first
    | exact superpose eq1677 eq5718
    | exact resolve eq5718 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5718
  have eq5936 : ∀ X0 X1 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 (M.op x y)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq5843 X0 X1 X3 X4 x
       have i₂ := eq1015 X0 x
       grind)
    | exact superpose eq1015 eq5843
    | exact resolve eq5843 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5843
  have eq6023 : ∀ X0 X1 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) := by
    intro X0 X1 X3 X4
    first
    | exact superpose eq1677 eq5936
    | exact resolve eq5936 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5936
  have eq6105 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op X3 X3) (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6023 X0 X1 X3 x
       have i₂ := eq1015 (M.op X3 X3) x
       grind)
    | exact superpose eq1015 eq6023
    | exact resolve eq6023 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6023
  have eq6181 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1209 eq6105
    | exact resolve eq6105 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6105
  have eq6237 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1677 eq6181
    | exact resolve eq6181 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6181
  have eq6602 : ∀ X0 X1 X2 X3 X4 X5 : G, (k X1 X0) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op X2 X2)))) ∨ X0 = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq576 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X2 X2)))) X1 X2
       have i₂ := eq261 (M.op X1 (M.op X2 X2)) X1 X2 X3 X4
       grind)
    | exact superpose eq261 eq576
    | exact resolve eq576 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq576
  have eq6619 : ∀ X0 X1 X3 X4 X5 : G, (k X1 X0) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op (σ x) (σ y))))) ∨ X0 = X1 := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq6602 X0 X1 x X3 X4 X5
       have i₂ := eq1015 X1 x
       grind)
    | exact superpose eq1015 eq6602
    | (have j0 := eq6602 (k X1 X0) (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op (σ x) (σ y))))) x X3 X4 X5
       grind)
    | exact resolve eq6602 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6602
  have eq6674 : ∀ X0 X1 X3 X4 X5 : G, (k X1 X0) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op x y)))) ∨ X0 = X1 := by
    intro X0 X1 X3 X4 X5
    first
    | exact superpose eq1677 eq6619
    | (have j0 := eq6619 (k X1 X0) (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op x y)))) X3 X4 X5
       grind)
    | exact resolve eq6619 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6619
  have eq6729 : ∀ X0 X1 X3 X4 : G, (k X1 X0) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 (M.op x y)))) ∨ X0 = X1 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq6674 X0 X1 X3 X4 x
       have i₂ := eq1015 X0 x
       grind)
    | exact superpose eq1015 eq6674
    | (have j0 := eq6674 (k X1 X0) (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 (M.op x y)))) X3 X4 x
       grind)
    | exact resolve eq6674 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6674
  have eq6777 : ∀ X0 X1 X3 X4 : G, (k X1 X0) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) ∨ X0 = X1 := by
    intro X0 X1 X3 X4
    first
    | exact superpose eq1677 eq6729
    | (have j0 := eq6729 (k X1 X0) (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) X3 X4
       grind)
    | exact resolve eq6729 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6729
  have eq6820 : ∀ X0 X1 X3 : G, (k X1 X0) = (M.op (M.op (M.op X3 X3) (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) ∨ X0 = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6777 X0 X1 X3 x
       have i₂ := eq1015 (M.op X3 X3) x
       grind)
    | exact superpose eq1015 eq6777
    | (have j0 := eq6777 (k X1 X0) (M.op (M.op (M.op X3 X3) (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) X3 x
       grind)
    | exact resolve eq6777 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6777
  have eq6857 : ∀ X0 X1 : G, (k X1 X0) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq1209 eq6820
    | (have j0 := eq6820 (k X1 X0) (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) x
       grind)
    | exact resolve eq6820 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209 eq6820
  have eq6894 : ∀ X0 X1 : G, (k X1 X0) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq1677 eq6857
    | (have j0 := eq6857 (k X1 X0) (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y))))
       grind)
    | exact resolve eq6857 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6857
  have eq6916 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq6237 eq6894
    | (have j0 := eq6894 (M.op X0 X1) (k X1 X0)
       grind)
    | exact resolve eq6894 eq6237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6237 eq6894
  have eq42153 : ∀ X0 : G, (k (M.op x y) X0) = (k X0 (M.op x y)) ∨ (M.op x y) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq5179 eq6916
    | (have j0 := eq6916 (k (M.op x y) X0) (k X0 (M.op x y))
       have j1 := eq5179 X0
       grind)
    | exact resolve eq6916 eq5179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6916
  have eq42208 : ∀ X0 : G, (k (M.op x y) X0) = (k X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have j0 := eq42153 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42153
  have eq43606 : (τ (k (M.op x y) (σ (M.op x y)))) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq42208 eq68
    | (have j1 := eq42208 (σ (M.op x y))
       grind)
    | exact resolve eq68 eq42208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq42208
  have eq43617 : (τ (k (M.op x y) (σ (M.op x y)))) = (k (M.op x y) (τ (M.op x y))) := by
    first
    | (have r₁ := eq43606
       have r₂ := eq1757
       grind)
    | exact resolve eq43606 eq1757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43606
  have eq43626 : (k (τ (M.op x y)) (M.op x y)) = (k (M.op x y) (τ (M.op x y))) := by
    first
    | exact superpose eq88 eq43617
    | exact resolve eq43617 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43617
  have eq43640 : (k (σ (τ (M.op x y))) (σ (M.op x y))) = (σ (k (M.op x y) (τ (M.op x y)))) := by
    first
    | exact superpose eq43626 eq15
    | exact resolve eq15 eq43626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43641 : (k (σ (τ (M.op x y))) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (τ (M.op x y)))) := by
    first
    | (have i₁ := eq43640
       have i₂ := eq15 sF2 (τ sF2)
       grind)
    | exact superpose eq15 eq43640
    | exact resolve eq43640 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43640
  have eq43644 : (k (M.op x y) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq43641
       have i₂ := eq36 sF2
       grind)
    | exact superpose eq36 eq43641
    | exact resolve eq43641 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43641
  have eq43646 : (k (σ (M.op x y)) (M.op x y)) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq43644
    | exact resolve eq43644 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43644
  have eq81906 : (σ (M.op x y)) = (M.op (k (M.op x y) (σ (M.op x y))) (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq43646 eq5034
    | (have j0 := eq5034 (σ (M.op x y)) (M.op (k (M.op x y) (σ (M.op x y))) (M.op (M.op x y) (M.op x y)))
       grind)
    | exact resolve eq5034 eq43646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5034
  have eq82091 : (σ (M.op x y)) = (M.op (k (M.op x y) (σ (M.op x y))) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have r₁ := eq81906
       have r₂ := eq1757
       grind)
    | exact resolve eq81906 eq1757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757 eq81906
  have eq82148 : (σ (M.op x y)) = (M.op (k (M.op x y) (σ (M.op x y))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq82091
       have i₂ := eq1015 (k sF2 sF3) sF2
       grind)
    | exact superpose eq1015 eq82091
    | exact resolve eq82091 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq82091
  have eq82187 : (σ (M.op x y)) = (M.op (k (M.op x y) (σ (M.op x y))) (M.op x y)) := by
    first
    | exact superpose eq1677 eq82148
    | exact resolve eq82148 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677 eq82148
  have eq82299 : (σ (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (σ (M.op x y)))) := by
    first
    | exact superpose eq82187 eq1729
    | exact resolve eq1729 eq82187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729
  have eq82302 : (σ (M.op x y)) = (k (k (M.op x y) (σ (M.op x y))) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq82187 eq5179
    | (have j0 := eq5179 (k (M.op x y) (σ (M.op x y)))
       grind)
    | exact resolve eq5179 eq82187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5179 eq82187
  have eq123361 : (τ (σ (M.op x y))) = (k (τ (k (M.op x y) (σ (M.op x y)))) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq82302 eq142
    | exact resolve eq142 eq82302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq82302
  have eq123379 : (τ (σ (M.op x y))) = (k (k (τ (M.op x y)) (M.op x y)) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq88 eq123361
    | exact resolve eq123361 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq123361
  have eq123387 : (τ (σ (M.op x y))) = (k (k (M.op x y) (τ (M.op x y))) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq43626 eq123379
    | exact resolve eq123379 eq43626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43626 eq123379
  have eq123394 : (M.op x y) = (k (k (M.op x y) (τ (M.op x y))) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq37 eq123387
    | exact resolve eq123387 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq123387
  have eq388300 : (k (M.op x y) (τ (M.op x y))) = (M.op (M.op x y) (M.op (τ (M.op x y)) (M.op x y))) ∨ (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq123394 eq5035
    | (have j0 := eq5035 (k (M.op x y) (τ (M.op x y))) (M.op (M.op x y) (M.op (τ (M.op x y)) (M.op x y)))
       grind)
    | exact resolve eq5035 eq123394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5035 eq123394
  have eq388303 : (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq1755 eq388300
    | exact resolve eq388300 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755 eq388300
  have eq388304 : (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by grind
  clear eq388303
  have eq388697 : (σ (τ (M.op x y))) = (k (σ (M.op x y)) (σ (τ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq388304 eq15
    | exact resolve eq15 eq388304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388304
  have eq388734 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq388697
       have i₂ := eq36 sF2
       grind)
    | exact superpose eq36 eq388697
    | exact resolve eq388697 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq388697
  have eq388749 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq388734
    | exact resolve eq388734 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq388734
  have eq388750 : (M.op x y) = (k (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq43646 eq388749
    | exact resolve eq388749 eq43646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43646 eq388749
  have eq388751 : (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by grind
  clear eq388750
  have eq388756 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq388751 eq82299
    | exact resolve eq82299 eq388751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82299 eq388751
  have eq388925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq388756
       have i₂ := eq1408 sF2
       grind)
    | exact superpose eq1408 eq388756
    | exact resolve eq388756 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408 eq388756
  have eq388977 : False := by grind
  exact eq388977
