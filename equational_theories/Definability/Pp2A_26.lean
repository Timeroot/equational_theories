import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pxx_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X0 X0) = X1 ∨ (M.op X2 X2) = (k X2 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 (k X1 X1) X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq46 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq12 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq56 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X0 X0) = X1 ∨ (M.op X2 X2) = (k X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq36 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq36 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq36 X0 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq36 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq67 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = (k X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq56 X0 X1 X2
       have j1 := eq48 (M.op X2 X2) X0
       grind)
    | (have r₁ := eq56 X1 X0 X2
       have r₂ := eq48 X0 X1
       grind)
    | (have r₁ := eq56 X0 (M.op X1 X1) X2
       have r₂ := eq48 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq56 X0 X1 X1
       have r₂ := eq48 (k X1 X1) X1
       grind)
    | exact resolve eq56 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq56
  have eq147 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq19
    | (have j1 := eq67 X1 X0
       grind)
    | exact resolve eq19 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq160 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op (M.op X1 X1) (M.op X1 X1)))) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 X1
       have i₂ := eq19 (M.op X1 X1) X1
       grind)
    | exact superpose eq19 eq147
    | (have j0 := eq147 X0 X1
       grind)
    | exact resolve eq147 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq147
  have eq167 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq160 X0 X1
       have i₂ := eq9 X1 X1
       grind)
    | exact superpose eq9 eq160
    | (have j0 := eq160 X0 X1
       grind)
    | exact resolve eq160 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq637 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq3648 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq637 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq3651 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3648 X0 X1
       have j1 := eq167 X0 X1
       grind)
    | (have r₁ := eq3648 X0 X1
       have r₂ := eq167 X0 X1
       grind)
    | (have r₁ := eq3648 X1 X1
       have r₂ := eq167 X1 X1
       grind)
    | exact resolve eq3648 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq3648
  have eq4601 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3651 (σ X0) (σ X1)
       grind)
    | exact superpose eq3651 eq15
    | exact resolve eq15 eq3651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4614 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4601 X0 X1
       have i₂ := eq3651 X0 X1
       grind)
    | exact superpose eq3651 eq4601
    | exact resolve eq4601 eq3651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3651 eq4601
  have eq4627 : False := by grind
  exact eq4627

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pyy_pxy_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq31 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq31
  have eq33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq77 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq10
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq103 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq33
    | (have j0 := eq33 X0 X1
       grind)
    | exact resolve eq33 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq148 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq123 x y
       grind)
    | exact superpose eq123 eq16
    | (have j1 := eq123 x y
       grind)
    | exact resolve eq16 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq410 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X1 (τ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq103
    | exact resolve eq103 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq103
  have eq418 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (M.op X2 (τ (M.op X0 (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq410 (M.op X0 X1) X2
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq410
    | exact resolve eq410 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq410
  have eq766 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq148
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq148
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq148
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq148
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq148 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq767 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq766
  have eq5167 : ∀ X0 X1 X2 : G, (τ (M.op X1 (M.op X1 X0))) = (M.op X2 (M.op X2 (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq418 X1 (M.op X1 X0) X2
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq418
    | exact resolve eq418 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq5567 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (σ (M.op X0 (M.op X0 (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op X2 (M.op X2 X1))
       have i₂ := eq5167 X1 X2 X0
       grind)
    | exact superpose eq5167 eq11
    | exact resolve eq11 eq5167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5167
  have eq9898 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq767
       grind)
    | exact superpose eq767 eq16
    | exact resolve eq16 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq9899 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq9898
       have r₂ := eq23 x
       grind)
    | exact resolve eq9898 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9898
  have eq10507 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X1 (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq5567 X1 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq5567
    | exact resolve eq5567 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5567
  have eq10780 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10507 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10507
    | exact resolve eq10507 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10507
  have eq714553 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9899
       grind)
    | exact superpose eq9899 eq10
    | exact resolve eq10 eq9899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9899
  have eq714963 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq714553
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq714553
    | exact resolve eq714553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714553
  have eq714978 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq714963
       grind)
    | exact superpose eq714963 eq16
    | exact resolve eq16 eq714963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714963
  have eq714979 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq714978
       have r₂ := eq23 x
       grind)
    | exact resolve eq714978 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq714978
  have eq715068 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq714979
       grind)
    | exact superpose eq714979 eq10
    | exact resolve eq10 eq714979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714979
  have eq715624 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq715068
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq715068
    | exact resolve eq715068 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715068
  have eq715625 : y = (M.op x x) := by grind
  clear eq715624
  have eq716256 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10780 x x
       have i₂ := eq715625
       grind)
    | exact superpose eq715625 eq10780
    | exact resolve eq10780 eq715625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10780 eq715625
  have eq716296 : False := by grind
  exact eq716296

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pxy_pxx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X0 X0) X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq78 x y
       grind)
    | exact superpose eq78 eq45
    | (have j1 := eq78 x y
       grind)
    | exact resolve eq45 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq105 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq25 eq37
  have eq109 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq105
    | exact resolve eq105 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq111 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq109
    | exact resolve eq109 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq109
  have eq137 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq16
    | exact resolve eq16 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq508 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq53 X0 x x X3
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq98 eq78
    | (have j0 := eq78 (σ x) (σ y)
       grind)
    | exact resolve eq78 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq98
  have eq1015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq1014
    | exact resolve eq1014 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1018 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1015
       have r₂ := eq28
       grind)
    | exact resolve eq1015 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1020 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1018 eq137
    | exact resolve eq137 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq1018
  have eq1035 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq1020
    | exact resolve eq1020 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1020
  have eq1036 : x = (M.op y y) := by grind
  clear eq1035
  have eq1055 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq1036
       grind)
    | exact superpose eq1036 eq111
    | exact resolve eq111 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq1057 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op X1 X0) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1
       have i₂ := eq1036
       grind)
    | exact superpose eq1036 eq14
    | exact resolve eq14 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1071 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1055
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1055
    | exact resolve eq1055 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1074 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq1071 eq14
    | exact resolve eq14 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1470 : y = (M.op (M.op x x) (M.op x x)) := by
    first
    | exact superpose eq503 eq1057
    | exact resolve eq1057 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq1057
  have eq1478 : y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq1470
       have i₂ := eq54 x x
       grind)
    | exact superpose eq54 eq1470
    | exact resolve eq1470 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1544 : x = (M.op x y) := by
    first
    | (have i₁ := eq508 x
       have i₂ := eq1478
       grind)
    | exact superpose eq1478 eq508
    | exact resolve eq508 eq1478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478
  have eq1555 : x = (M.op x y) := by
    first
    | (have i₁ := eq1544
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1544
    | exact resolve eq1544 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1544
  have eq1557 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1555 eq21
    | exact resolve eq21 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1555
  have eq1590 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1557
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1557
    | exact resolve eq1557 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1557
  have eq1595 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1590 eq27
    | exact resolve eq27 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2454 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1590 eq1074
    | exact resolve eq1074 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq1590
  have eq2721 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq2454 (M.op sF1 sF1) x
       have i₂ := eq598 sF1 x
       grind)
    | exact superpose eq598 eq2454
    | exact resolve eq2454 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq2454
  have eq2736 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq2721
       have i₂ := eq54 sF1 sF1
       grind)
    | exact superpose eq54 eq2721
    | exact resolve eq2721 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq2721
  have eq2776 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2736 eq508
    | exact resolve eq508 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq2736
  have eq2798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1595 eq2776
    | exact resolve eq2776 eq1595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595 eq2776
  have eq2801 : False := by grind
  exact eq2801

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (M.op x y) ≠ (M.op x x) ∨ (k y x) = (M.op y x) := by
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
  have eq65 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq44
    | exact resolve eq44 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq50
    | exact resolve eq50 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq70
  have eq96 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq96
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq105
    | exact resolve eq105 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq111
    | exact resolve eq111 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112
    | exact resolve eq112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq232 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq51 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq232 eq51
    | exact resolve eq51 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq53 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1196 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq234 eq51
    | exact resolve eq51 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq1213 : (M.op (M.op x y) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq232 eq1196
    | exact resolve eq1196 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq1709 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq583 X0 X0 X0
       grind)
    | exact superpose eq583 eq51
    | exact resolve eq51 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq1783 : (M.op x y) = (M.op y (M.op y (M.op y (M.op x y)))) := by
    first
    | exact superpose eq1213 eq238
    | exact resolve eq238 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq1213
  have eq2013 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq52 sF4
       have i₂ := eq1709 sF4
       grind)
    | exact superpose eq1709 eq52
    | exact resolve eq52 eq1709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1709
  have eq16416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16417 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16416
    | exact resolve eq16416 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16416
  have eq16426 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq16417
       have r₂ := eq28
       grind)
    | exact resolve eq16417 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16417
  have eq16429 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16426
    | exact resolve eq16426 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16426
  have eq16432 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16429 eq65
    | (have r₁ := eq65
       have r₂ := eq16429
       grind)
    | exact resolve eq65 eq16429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq16440 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16429 eq51
    | exact resolve eq51 eq16429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16429
  have eq16506 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq16432
  have eq16931 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16440 eq2013
    | exact resolve eq2013 eq16440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013 eq16440
  have eq17293 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16506 eq113
    | exact resolve eq113 eq16506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq16506
  have eq17303 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17293
  have eq17444 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17303 eq16931
    | exact resolve eq16931 eq17303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16931 eq17303
  have eq17475 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq17444
  have eq17482 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17475
       have r₂ := eq28
       grind)
    | exact resolve eq17475 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17475
  have eq17486 : (M.op x y) ≠ (M.op x y) ∨ (k y x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq64
       have i₂ := eq17482
       grind)
    | exact superpose eq17482 eq64
    | (have r₁ := eq64
       have r₂ := eq17482
       grind)
    | exact resolve eq64 eq17482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq17487 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq17482
       grind)
    | exact superpose eq17482 eq73
    | exact resolve eq73 eq17482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq17496 : x = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq17482
       grind)
    | exact superpose eq17482 eq51
    | exact resolve eq51 eq17482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq17482
  have eq17561 : (k y x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17486
  have eq17587 : x = (M.op y (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq232 eq17496
    | exact resolve eq17496 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq17496
  have eq17594 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq17487
    | exact resolve eq17487 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17487
  have eq18344 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq17561
       grind)
    | exact superpose eq17561 eq96
    | exact resolve eq96 eq17561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq17561
  have eq18637 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17587 eq1783
    | exact resolve eq1783 eq17587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783 eq17587
  have eq19135 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18344
       have i₂ := eq18637
       grind)
    | exact superpose eq18637 eq18344
    | exact resolve eq18344 eq18637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18344 eq18637
  have eq19186 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19135
  have eq19200 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq19186
    | exact resolve eq19186 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19186
  have eq19214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19200 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq19200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19200
  have eq19215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq19214
  have eq19219 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq19215
    | exact resolve eq19215 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19215
  have eq19228 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq19219
       have r₂ := eq28
       grind)
    | exact resolve eq19219 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19219
  have eq19231 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq19228
    | exact resolve eq19228 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19228
  have eq19298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19231 eq17594
    | exact resolve eq17594 eq19231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17594 eq19231
  have eq19367 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19298
  have eq19386 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq19367
       have r₂ := eq28
       grind)
    | exact resolve eq19367 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19367
  have eq19392 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq19386 eq30
    | exact resolve eq30 eq19386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19386
  have eq19520 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq19392
    | exact resolve eq19392 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19392
  have eq19521 : x = y := by grind
  clear eq19520
  have eq19533 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq19521
       grind)
    | exact superpose eq19521 eq19
    | exact resolve eq19 eq19521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq19534 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq19521
       grind)
    | exact superpose eq19521 eq25
    | exact resolve eq25 eq19521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq19521
  have eq19680 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq19534
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19534
    | exact resolve eq19534 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq19534
  have eq19703 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19680 eq27
    | exact resolve eq27 eq19680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19680
  have eq20036 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19703 eq72
    | exact resolve eq72 eq19703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq19703
  have eq20148 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq20036
       have i₂ := eq19533
       grind)
    | exact superpose eq19533 eq20036
    | exact resolve eq20036 eq19533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19533 eq20036
  have eq20175 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20148 eq15
    | exact resolve eq15 eq20148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20148
  have eq20225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq20175
    | exact resolve eq20175 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq20175
  have eq20239 : False := by grind
  exact eq20239

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq136 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq56 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq56
    | exact resolve eq56 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq190 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq136 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq136 X0 X1
       grind)
    | exact superpose eq136 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq136 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq136 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq136 X1 X1
       grind)
    | exact resolve eq13 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X2 X2))) = X2 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X0
       have i₂ := eq136 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq136 X0 X1
       grind)
    | exact superpose eq136 eq9
    | (have j1 := eq136 X0 X1
       grind)
    | exact resolve eq9 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq197 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq200 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq197 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq197 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq218 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq145 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq65 X1 X1
       grind)
    | exact superpose eq65 eq145
    | exact resolve eq145 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq145
  have eq360 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq200 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq597 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X2) (M.op X1 (M.op X0 X1)))) ∨ (M.op X3 X2) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq193 X2 X3 (M.op X0 X1)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq193
    | (have j0 := eq193 X2 X3 X2
       grind)
    | exact resolve eq193 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq193
  have eq13800 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq597 X0 X0 X0 X1
       have i₂ := eq218 X0 X0
       grind)
    | exact superpose eq218 eq597
    | (have j0 := eq597 X0 X1 X0 X1
       grind)
    | exact resolve eq597 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq597
  have eq13949 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13800 X0 X1
       have j1 := eq360 X0 X1
       grind)
    | (have r₁ := eq13800 X0 X1
       have r₂ := eq360 X0 X1
       grind)
    | (have r₁ := eq13800 X0 X0
       have r₂ := eq360 X0 X0
       grind)
    | exact resolve eq13800 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq13800
  have eq14077 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq13949 (σ X0) (σ X1)
       grind)
    | exact superpose eq13949 eq15
    | exact resolve eq15 eq13949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14087 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14077 X0 X1
       have i₂ := eq13949 X0 X1
       grind)
    | exact superpose eq13949 eq14077
    | exact resolve eq14077 eq13949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13949 eq14077
  have eq14229 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14087 y x
       grind)
    | exact superpose eq14087 eq16
    | (have r₁ := eq16
       have r₂ := eq14087 y x
       grind)
    | exact resolve eq16 eq14087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14087
  have eq14278 : False := by grind
  exact eq14278

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq90 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq89
    | exact resolve eq89 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq51 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq102 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq102
    | (have j0 := eq102 (σ X0)
       grind)
    | exact resolve eq102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq102 x
       grind)
    | exact superpose eq102 eq44
    | (have j1 := eq102 x
       grind)
    | exact resolve eq44 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq379 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq51
    | exact resolve eq51 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq53 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq53 X0 x x X3
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq1313 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq192 eq445
    | exact resolve eq445 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq1331 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq445 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq445 X0 X0 X0
       grind)
    | exact superpose eq445 eq445
    | exact resolve eq445 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1363 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  have eq1364 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq445 X0 X0 X0
       grind)
    | exact superpose eq445 eq51
    | exact resolve eq51 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1372 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq379 (M.op x (M.op x x))
       have i₂ := eq445 x x x
       grind)
    | exact superpose eq445 eq379
    | exact resolve eq379 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq445
  have eq1387 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1363 X0
       have i₂ := eq476 X0 X0
       grind)
    | exact superpose eq476 eq1363
    | exact resolve eq1363 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq1363
  have eq1408 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op x y) (M.op y (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq191 eq1313
    | exact resolve eq1313 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq2038 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1372 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq1372
    | exact resolve eq1372 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq2079 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2038 X0 X1
       have i₂ := eq1364 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq1364 eq2038
    | exact resolve eq2038 eq1364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038
  have eq2093 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2079 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2079
    | exact resolve eq2079 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq4427 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq341 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq37529 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2093 eq14
    | exact resolve eq14 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093
  have eq38031 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X0)) (M.op (M.op X0 (M.op y X0)) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq37529 eq1331
    | exact resolve eq1331 eq37529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331 eq37529
  have eq38056 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X0)) (M.op (M.op X0 (M.op y X0)) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq191 eq38031
    | exact resolve eq38031 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq38031
  have eq38105 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq38056 X0 X1
       have i₂ := eq1364 (M.op X0 (M.op y X0))
       grind)
    | exact superpose eq1364 eq38056
    | exact resolve eq38056 eq1364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364 eq38056
  have eq38132 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq391 eq38105
    | exact resolve eq38105 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq38105
  have eq39916 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op y (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq38132 eq1408
    | exact resolve eq1408 eq38132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408 eq38132
  have eq45343 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq39916 X0 y
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq39916
    | exact resolve eq39916 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq45404 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f45404_13 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
      intro X0
      grind
    have f45404_14 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op y (M.op X1 X1))) = X1 := by
      intro X0 X1
      grind
    have f45404_22 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) := by grind
    have f45404_23 : y ≠ x := by grind
    have f45404_24 : y ≠ (M.op x x) := by grind
    have f45404_26 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x x))) ∨ y = (M.op x x) := by
      intro X0
      first
      | (have j0 := f45404_13 X0
         grind)
      | (have r₁ := f45404_13 X0
         have r₂ := f45404_22
         grind)
      | exact resolve f45404_13 f45404_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f45404_27 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x x))) := by
      intro X0
      first
      | (have j0 := f45404_26 X0
         grind)
      | (have r₁ := f45404_26 X0
         have r₂ := f45404_24
         grind)
      | exact resolve f45404_26 f45404_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f45404_28 : y = x := by
      first
      | (have i₁ := f45404_27 x
         have i₂ := f45404_14 x x
         grind)
      | exact superpose f45404_14 f45404_27
      | exact resolve f45404_27 f45404_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f45404_29 : False := by
      first
      | (have r₁ := f45404_28
         have r₂ := f45404_23
         grind)
      | exact resolve f45404_28 f45404_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f45404_29
  clear eq45343
  have eq72945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq45404 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq45404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq72945
    | exact resolve eq72945 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72945
  have eq72957 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq72946
       have r₂ := eq28
       grind)
    | exact resolve eq72946 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72946
  have eq73050 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op (σ x) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq72957 eq39916
    | exact resolve eq39916 eq72957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72957
  have eq73133 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq39916 eq73050
    | exact resolve eq73050 eq39916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39916 eq73050
  have eq73191 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq73133
  have eq73397 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq73191
    | exact resolve eq73191 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73191
  have eq75700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq73397 eq45404
    | exact resolve eq45404 eq73397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45404 eq73397
  have eq75702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq75700
  have eq75704 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq75702
       have r₂ := eq28
       grind)
    | exact resolve eq75702 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75702
  have eq75707 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq345
       have i₂ := eq75704
       grind)
    | exact superpose eq75704 eq345
    | exact resolve eq345 eq75704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75711 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq75704
  have eq75848 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq75707
  have eq75939 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75711
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75711
    | exact resolve eq75711 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75711
  have eq75941 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75848
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq75848
    | exact resolve eq75848 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75848
  have eq79026 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq75939
       grind)
    | exact superpose eq75939 eq70
    | exact resolve eq70 eq75939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq75939
  have eq79044 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq79026
    | exact resolve eq79026 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79026
  have eq79045 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq75941
       have i₂ := eq102 sF2
       grind)
    | exact superpose eq102 eq75941
    | (have j1 := eq102 (σ x)
       grind)
    | exact resolve eq75941 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209670 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq79045
  have eq209942 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq209670
    | exact resolve eq209670 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209670
  have eq212630 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq209942 eq79044
    | exact resolve eq79044 eq209942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79044 eq209942
  have eq212634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq212630
  have eq212644 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq212634
       have r₂ := eq28
       grind)
    | exact resolve eq212634 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212634
  have eq212654 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq212907 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq212654 eq75941
    | exact resolve eq75941 eq212654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75941 eq212654
  have eq212923 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq212907
  have eq212933 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq212923 eq212644
    | exact resolve eq212644 eq212923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212644 eq212923
  have eq213124 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq212933
  have eq213252 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq213124 eq30
    | exact resolve eq30 eq213124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq213124
  have eq213492 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq213252
    | exact resolve eq213252 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq213252
  have eq213493 : x = y := by grind
  clear eq213492
  have eq213499 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq213493
       grind)
    | exact superpose eq213493 eq19
    | exact resolve eq19 eq213493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq213500 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq213493
       grind)
    | exact superpose eq213493 eq25
    | exact resolve eq25 eq213493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq213493
  have eq213914 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq213500
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq213500
    | exact resolve eq213500 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213500
  have eq213939 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq213914 eq27
    | exact resolve eq27 eq213914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq213914
  have eq214242 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq345
       have i₂ := eq213499
       grind)
    | exact superpose eq213499 eq345
    | exact resolve eq345 eq213499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq214336 : (M.op x y) = (k x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq1387 x
       have i₂ := eq213499
       grind)
    | exact superpose eq213499 eq1387
    | exact resolve eq1387 eq213499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq214586 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq214242
    | exact resolve eq214242 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214242
  have eq215767 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  have eq228654 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq214586 eq102
    | (have j0 := eq102 (σ x)
       grind)
    | exact resolve eq102 eq214586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq228655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq213939 eq228654
    | exact resolve eq228654 eq213939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228654
  have eq228670 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq228655
       have r₂ := eq28
       grind)
    | exact resolve eq228655 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228655
  have eq228676 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq213939 eq228670
    | exact resolve eq228670 eq213939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228670
  have eq228795 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq228676 eq215767
    | exact resolve eq215767 eq228676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215767 eq228676
  have eq228811 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq213939 eq228795
    | exact resolve eq228795 eq213939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228795
  have eq229336 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq228811 eq214586
    | exact resolve eq214586 eq228811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214586 eq228811
  have eq229342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq229336
  have eq229346 : x = (M.op x y) := by
    first
    | (have r₁ := eq229342
       have r₂ := eq28
       grind)
    | exact resolve eq229342 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229342
  have eq229357 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq229346 eq21
    | exact resolve eq21 eq229346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq229822 : x = (k x (M.op x x)) := by
    first
    | exact superpose eq229346 eq214336
    | exact resolve eq214336 eq229346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214336
  have eq229834 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq229822
       have i₂ := eq213499
       grind)
    | exact superpose eq213499 eq229822
    | exact resolve eq229822 eq213499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213499 eq229822
  have eq230094 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq229357
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq229357
    | exact resolve eq229357 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229357
  have eq230097 : x = (k x x) := by
    first
    | exact superpose eq229346 eq229834
    | exact resolve eq229834 eq229346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229346 eq229834
  have eq231824 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4427 x
       have i₂ := eq230097
       grind)
    | exact superpose eq230097 eq4427
    | (have j0 := eq4427 x
       grind)
    | exact resolve eq4427 eq230097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4427 eq230097
  have eq231828 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq231824
  have eq231837 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq231828
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq231828
    | exact resolve eq231828 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq231828
  have eq231855 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq213939 eq231837
    | exact resolve eq231837 eq213939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213939 eq231837
  have eq231871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq230094 eq231855
    | exact resolve eq231855 eq230094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230094 eq231855
  have eq231885 : False := by grind
  exact eq231885

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq175 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq602
       grind)
    | exact superpose eq602 eq40
    | exact resolve eq40 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq630
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq630
    | exact resolve eq630 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq633 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq631
    | exact resolve eq631 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq643 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq633 eq610
    | exact resolve eq610 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq643
       have r₂ := eq27
       grind)
    | exact resolve eq643 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq686 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq178 X0 (M.op X0 X0)
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq178
    | exact resolve eq178 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq178 X0 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op X1 X0)
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq176
    | exact resolve eq176 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq710 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op X1 X0)
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq175
    | exact resolve eq175 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq702 X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq702
    | exact resolve eq702 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq725 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq650 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq650
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq650
       grind)
    | exact resolve eq12 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq725
  have eq731 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq633 eq729
    | exact resolve eq729 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq808 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq731 eq179
    | exact resolve eq179 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq813 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq808
    | exact resolve eq808 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq633 eq813
    | exact resolve eq813 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq813
  have eq816 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq815
       have r₂ := eq27
       grind)
    | exact resolve eq815 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq822 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq816
       grind)
    | exact superpose eq816 eq16
    | exact resolve eq16 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1755 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq177 X1 x x X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1757 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq178 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq177 X0 x x X3
       grind)
    | exact superpose eq177 eq178
    | exact resolve eq178 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq16576 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq709 X0 X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq709
    | exact resolve eq709 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21525 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op y X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq822 (M.op X0 (M.op X0 X0))
       have i₂ := eq1755 X0 X0 X0
       grind)
    | exact superpose eq1755 eq822
    | exact resolve eq822 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq21546 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1757 (M.op x (M.op x x)) x
       have i₂ := eq1755 x x x
       grind)
    | exact superpose eq1755 eq1757
    | exact resolve eq1757 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq21606 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21546 X0 X1
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq21546
    | exact resolve eq21546 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21546
  have eq21627 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op x (M.op y X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq21525 X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq21525
    | exact resolve eq21525 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21525
  have eq21811 : (M.op y x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (k (M.op x x) x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq709 x y
       have i₂ := eq21627 x
       grind)
    | exact superpose eq21627 eq709
    | exact resolve eq709 eq21627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21627
  have eq21883 : (M.op y x) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16576 eq21811
    | exact resolve eq21811 eq16576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21811
  have eq21905 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq816 eq21883
    | exact resolve eq21883 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq21883
  have eq21940 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq21905
       grind)
    | exact superpose eq21905 eq179
    | exact resolve eq179 eq21905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21905
  have eq22101 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq21940
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21940
    | exact resolve eq21940 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21940
  have eq22428 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq22101
       grind)
    | exact superpose eq22101 eq40
    | exact resolve eq40 eq22101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22101
  have eq22434 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq22428
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22428
    | exact resolve eq22428 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq22428
  have eq22436 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq22434
    | exact resolve eq22434 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22434
  have eq22645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22436 eq610
    | exact resolve eq610 eq22436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq22656 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq22645
       have r₂ := eq27
       grind)
    | exact resolve eq22645 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22645
  have eq22687 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22656 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq22656
       grind)
    | exact resolve eq12 eq22656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22656
  have eq22733 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq22687
  have eq22742 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22436 eq22733
    | exact resolve eq22733 eq22436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22733
  have eq22743 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq22742
  have eq22934 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22743 eq179
    | exact resolve eq179 eq22743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22743
  have eq23080 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq22934
    | exact resolve eq22934 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22934
  have eq23091 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22436 eq23080
    | exact resolve eq23080 eq22436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22436 eq23080
  have eq23102 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq23091
       have r₂ := eq27
       grind)
    | exact resolve eq23091 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23091
  have eq23108 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq23102 eq29
    | exact resolve eq29 eq23102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq23135 : y = (M.op x y) := by
    first
    | exact superpose eq23108 eq32
    | exact resolve eq32 eq23108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq23140 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23108 eq14
    | exact resolve eq14 eq23108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23108
  have eq23141 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq23135
       grind)
    | exact superpose eq23135 eq18
    | exact resolve eq18 eq23135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq23145 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq23135
       grind)
    | exact superpose eq23135 eq175
    | exact resolve eq175 eq23135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq23148 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq602
       have i₂ := eq23135
       grind)
    | exact superpose eq23135 eq602
    | exact resolve eq602 eq23135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq23149 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x y) (M.op (M.op x y) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq710 X1 X0
       have i₂ := eq23135
       grind)
    | exact superpose eq23135 eq710
    | exact resolve eq710 eq23135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq24174 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq23145 (M.op X0 (M.op X0 X0))
       have i₂ := eq1755 X0 X0 X0
       grind)
    | exact superpose eq1755 eq23145
    | exact resolve eq23145 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26647 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq23148 eq40
    | exact resolve eq40 eq23148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq23148
  have eq26658 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq20 eq26647
    | exact resolve eq26647 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26647
  have eq26661 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq23102 eq26658
    | exact resolve eq26658 eq23102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26658
  have eq26823 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1755 X0 X1 X0
       have i₂ := eq24174 X0
       grind)
    | (have i₁ := eq1755 (M.op x y) X1 (M.op x y)
       have i₂ := eq24174 (M.op x y)
       grind)
    | exact superpose eq24174 eq1755
    | exact resolve eq1755 eq24174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq26905 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq178 X0 (M.op X0 X0)
       have i₂ := eq24174 X0
       grind)
    | exact superpose eq24174 eq178
    | exact resolve eq178 eq24174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26943 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = (M.op (M.op (M.op x y) X0) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq26905 X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq26905
    | exact resolve eq26905 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26905
  have eq26983 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq26943 X0
       have i₂ := eq21606 X0 sF0
       grind)
    | exact superpose eq21606 eq26943
    | exact resolve eq26943 eq21606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26943
  have eq32192 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op (M.op x y) (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq23149 X0 X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq23149
    | exact resolve eq23149 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23149
  have eq33784 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq26823 X0 X0
       have i₂ := eq24174 X0
       grind)
    | (have i₁ := eq26823 (M.op x y) (M.op x y)
       have i₂ := eq24174 (M.op x y)
       grind)
    | exact superpose eq24174 eq26823
    | exact resolve eq26823 eq24174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24174
  have eq33877 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq32192 eq26823
    | exact resolve eq26823 eq32192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26823 eq32192
  have eq34026 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 (M.op (M.op X0 X0) (k (M.op X0 X0) X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33877 X0 X1
       have i₂ := eq686 X0
       grind)
    | exact superpose eq686 eq33877
    | exact resolve eq33877 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq33877
  have eq34058 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq33784 X0
       have i₂ := eq178 sF0 (M.op sF0 X0)
       grind)
    | exact superpose eq178 eq33784
    | exact resolve eq33784 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33784
  have eq34081 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34026 X0 X1
       have i₂ := eq21606 X0 X0
       grind)
    | exact superpose eq21606 eq34026
    | exact resolve eq34026 eq21606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21606 eq34026
  have eq34149 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 X0)) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq23145 eq34058
    | exact resolve eq34058 eq23145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34058
  have eq34331 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq34149 eq23145
    | exact resolve eq23145 eq34149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23145 eq34149
  have eq36637 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (k (M.op X0 X0) X0) X1 X2
       have i₂ := eq26983 X0
       grind)
    | exact superpose eq26983 eq16
    | exact resolve eq16 eq26983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26983
  have eq42367 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (k (M.op X0 X0) X0))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq709 X0 (M.op X1 X0)
       have i₂ := eq36637 X0 X0 X1
       grind)
    | exact superpose eq36637 eq709
    | exact resolve eq709 eq36637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq36637
  have eq42454 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq16576 eq42367
    | exact resolve eq42367 eq16576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16576 eq42367
  have eq43028 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq650 eq42454
    | exact resolve eq42454 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42454
  have eq43322 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq43028
       have i₂ := eq23135
       grind)
    | exact superpose eq23135 eq43028
    | exact resolve eq43028 eq23135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43028
  have eq44245 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq43322 eq650
    | exact resolve eq650 eq43322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq43322
  have eq44287 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq44245
       have i₂ := eq23135
       grind)
    | exact superpose eq23135 eq44245
    | exact resolve eq44245 eq23135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23135 eq44245
  have eq44288 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq44287
  have eq44308 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq44288 eq179
    | exact resolve eq179 eq44288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq44319 : (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq44288 eq714
    | exact resolve eq714 eq44288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq44288
  have eq44459 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq26661 eq44319
    | exact resolve eq44319 eq26661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44319
  have eq44462 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq26 eq44308
    | exact resolve eq44308 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44308
  have eq44495 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq44459
    | exact resolve eq44459 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44459
  have eq44498 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq26661 eq44462
    | exact resolve eq44462 eq26661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26661 eq44462
  have eq44524 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq44495 eq44498
    | exact resolve eq44498 eq44495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44498
  have eq44558 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44495 eq34331
    | exact resolve eq34331 eq44495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44572 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44495 eq178
    | exact resolve eq178 eq44495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44495
  have eq44615 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23141 eq44572
    | exact resolve eq44572 eq23141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44572
  have eq44620 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23141 eq44558
    | exact resolve eq44558 eq23141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44558
  have eq44634 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44615 eq44620
    | exact resolve eq44620 eq44615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44615 eq44620
  have eq44645 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44634 eq27
    | exact resolve eq27 eq44634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44634
  have eq44918 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23102 eq44645
    | exact resolve eq44645 eq23102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44645
  have eq45108 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq44524 eq34331
    | exact resolve eq34331 eq44524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34331
  have eq45122 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq44524 eq178
    | exact resolve eq178 eq44524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq44524
  have eq45165 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23141 eq45122
    | exact resolve eq45122 eq23141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45122
  have eq45170 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23141 eq45108
    | exact resolve eq45108 eq23141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45108
  have eq45185 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq45165 eq45170
    | exact resolve eq45170 eq45165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45165 eq45170
  have eq45193 : x = (M.op x y) := by
    first
    | (have r₁ := eq45185
       have r₂ := eq44918
       grind)
    | exact resolve eq45185 eq44918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44918 eq45185
  have eq45198 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq45193
       grind)
    | exact superpose eq45193 eq22
    | exact resolve eq22 eq45193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq45287 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq23141
       have i₂ := eq45193
       grind)
    | exact superpose eq45193 eq23141
    | exact resolve eq23141 eq45193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23141 eq45193
  have eq45311 : (σ x) = (σ y) := by
    first
    | exact superpose eq45198 eq23140
    | exact resolve eq23140 eq45198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23140
  have eq45312 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq45198 eq20
    | exact resolve eq20 eq45198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45198
  have eq45420 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq45311 eq26
    | exact resolve eq26 eq45311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq46371 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq45287 eq34081
    | exact resolve eq34081 eq45287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34081
  have eq46374 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq45287 eq46371
    | exact resolve eq46371 eq45287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45287 eq46371
  have eq46529 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq46374 eq38
    | exact resolve eq38 eq46374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq46374
  have eq46544 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq46529
    | exact resolve eq46529 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq46529
  have eq46550 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq23102 eq46544
    | exact resolve eq46544 eq23102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23102 eq46544
  have eq46556 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq45311 eq46550
    | exact resolve eq46550 eq45311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45311 eq46550
  have eq46655 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45420 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq45420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq45420
  have eq46699 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46556 eq46655
    | exact resolve eq46655 eq46556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46556 eq46655
  have eq46700 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq46699
  have eq46827 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq46700 eq27
    | exact resolve eq27 eq46700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq46700
  have eq47123 : False := by grind
  exact eq47123

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyy_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq636 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq662 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq620 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq834 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq847 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq177 X0 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op X1 X0)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq175
    | exact resolve eq175 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq847 X0
       grind)
    | exact superpose eq847 eq16
    | exact resolve eq16 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq834 eq16
    | exact resolve eq16 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq960 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq947 X0
       have i₂ := eq177 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq177 eq947
    | exact resolve eq947 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq965 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq960 X0
       have i₂ := eq177 X0 X0
       grind)
    | exact superpose eq177 eq960
    | exact resolve eq960 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq1078 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | exact superpose eq180 eq177
    | exact resolve eq177 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1127 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1078 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq1078
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq1078 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1153 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1347 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq626
       grind)
    | exact superpose eq626 eq39
    | exact resolve eq39 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq1348 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1347
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1347
    | exact resolve eq1347 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347
  have eq1350 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1348
    | exact resolve eq1348 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq1843 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq856 (M.op X0 X0) X0
       have i₂ := eq965 X0
       grind)
    | exact superpose eq965 eq856
    | exact resolve eq856 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq1991 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq847 X0
       have i₂ := eq1843 X0
       grind)
    | exact superpose eq1843 eq847
    | exact resolve eq847 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq2078 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq175 eq1991
    | exact resolve eq1991 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq1991
  have eq2646 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 (M.op (M.op X2 X1) (k X0 X0))
       have i₂ := eq662 X0 X1 X2
       grind)
    | exact superpose eq662 eq177
    | (have j1 := eq662 X0 X1 X2
       grind)
    | exact resolve eq177 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq2661 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1153 eq2646
    | (have j0 := eq2646 X0 x x
       have j1 := eq1153 X0 x
       grind)
    | exact resolve eq2646 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153 eq2646
  have eq2683 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2661 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq2661 x
       have r₂ := eq13 (k x x) x
       grind)
    | (have r₁ := eq2661 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq2661 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq2661 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2661
  have eq2724 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2078 X0
       have i₂ := eq2683 X0
       grind)
    | exact superpose eq2683 eq2078
    | exact resolve eq2078 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078
  have eq2725 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq2683 X0
       grind)
    | exact superpose eq2683 eq16
    | exact resolve eq16 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2727 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 X0
       have i₂ := eq2683 X0
       grind)
    | exact superpose eq2683 eq177
    | exact resolve eq177 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq2732 : ∀ X0 : G, (k X0 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq856 X0 X0
       have i₂ := eq2683 X0
       grind)
    | exact superpose eq2683 eq856
    | exact resolve eq856 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2789 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2727 X0
       have i₂ := eq2683 (k X0 X0)
       grind)
    | exact superpose eq2683 eq2727
    | exact resolve eq2727 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727
  have eq2790 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2725 X0 X1
       have i₂ := eq2683 X1
       grind)
    | exact superpose eq2683 eq2725
    | exact resolve eq2725 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq3138 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (k X1 X1) (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2790 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq2790
    | exact resolve eq2790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2790
  have eq9113 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq898 X0 X0
       grind)
    | exact superpose eq898 eq16
    | exact resolve eq16 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq9184 : ∀ X0 X1 X2 : G, (M.op X0 (k X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9113 X0 X1 X2
       have i₂ := eq2683 X0
       grind)
    | exact superpose eq2683 eq9113
    | exact resolve eq9113 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9113
  have eq24668 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ X0))) = (M.op (k (σ (k X0 X0)) (σ (k X0 X0))) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq856 (σ (k X0 X0)) (k (σ (k X0 X0)) (σ (k X0 X0)))
       have i₂ := eq3138 X0 (σ (k X0 X0))
       grind)
    | exact superpose eq3138 eq856
    | exact resolve eq856 eq3138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3138
  have eq24728 : ∀ X0 : G, (k (σ (k X0 X0)) (σ (k X0 X0))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq24668 X0
       have i₂ := eq2724 (σ (k X0 X0))
       grind)
    | exact superpose eq2724 eq24668
    | exact resolve eq24668 eq2724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24668
  have eq24766 : ∀ X0 : G, (σ (k (k X0 X0) (k X0 X0))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq24728 X0
       have i₂ := eq10 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq10 eq24728
    | exact resolve eq24728 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24728
  have eq24792 : ∀ X0 : G, (σ (M.op X0 (k X0 X0))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq24766 X0
       have i₂ := eq2789 X0
       grind)
    | exact superpose eq2789 eq24766
    | exact resolve eq24766 eq2789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2789 eq24766
  have eq25371 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (k X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq856 X0 (M.op X1 X0)
       have i₂ := eq9184 X0 X0 X1
       grind)
    | exact superpose eq9184 eq856
    | exact resolve eq856 eq9184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856 eq9184
  have eq25434 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq2732 eq25371
    | exact resolve eq25371 eq2732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732 eq25371
  have eq116366 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1350 eq636
    | exact resolve eq636 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636 eq1350
  have eq116377 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq116366
       have r₂ := eq27
       grind)
    | exact resolve eq116366 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116366
  have eq116385 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq116377
       have i₂ := eq2683 sF2
       grind)
    | exact superpose eq2683 eq116377
    | exact resolve eq116377 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116377
  have eq116391 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq116385
       have i₂ := eq2683 x
       grind)
    | exact superpose eq2683 eq116385
    | exact resolve eq116385 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116385
  have eq117820 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq116391 eq2724
    | exact resolve eq2724 eq116391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116391
  have eq117901 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by grind
  clear eq117820
  have eq118013 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq117901 eq25434
    | exact resolve eq25434 eq117901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118043 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq117901 eq118013
    | exact resolve eq118013 eq117901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117901 eq118013
  have eq118118 : (τ (σ y)) = (k x x) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq118043 eq97
    | exact resolve eq97 eq118043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq118043
  have eq118310 : y = (k x x) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq118118
    | exact resolve eq118118 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq118118
  have eq118311 : y = (k x x) ∨ y = (M.op y x) := by grind
  clear eq118310
  have eq118397 : y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2724 x
       have i₂ := eq118311
       grind)
    | exact superpose eq118311 eq2724
    | exact resolve eq2724 eq118311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724 eq118311
  have eq118478 : y = (M.op y x) := by grind
  clear eq118397
  have eq118589 : (k x x) = (M.op y x) := by
    first
    | (have i₁ := eq25434 x y
       have i₂ := eq118478
       grind)
    | exact superpose eq118478 eq25434
    | exact resolve eq25434 eq118478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25434
  have eq118619 : y = (k x x) := by
    first
    | (have i₁ := eq118589
       have i₂ := eq118478
       grind)
    | exact superpose eq118478 eq118589
    | exact resolve eq118589 eq118478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118478 eq118589
  have eq118712 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq118619
       grind)
    | exact superpose eq118619 eq39
    | exact resolve eq39 eq118619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq118784 : (σ (M.op x y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | (have i₁ := eq24792 x
       have i₂ := eq118619
       grind)
    | exact superpose eq118619 eq24792
    | exact resolve eq24792 eq118619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24792 eq118619
  have eq118833 : (σ (M.op x y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | (have i₁ := eq118784
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq118784
    | exact resolve eq118784 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118784
  have eq118891 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq118712
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq118712
    | exact resolve eq118712 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq118712
  have eq118909 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1843 eq118833
    | exact resolve eq118833 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843 eq118833
  have eq118949 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq118891
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq118891
    | exact resolve eq118891 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq118891
  have eq118959 : (σ (M.op x y)) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq118909
       have i₂ := eq2683 sF2
       grind)
    | exact superpose eq2683 eq118909
    | exact resolve eq118909 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683 eq118909
  have eq118986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq118949 eq118959
    | exact resolve eq118959 eq118949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118949 eq118959
  have eq119005 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq118986
    | exact resolve eq118986 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq118986
  have eq119020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq119005
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119005
    | exact resolve eq119005 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq119005
  have eq119029 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq119020
    | exact resolve eq119020 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq119020
  have eq119035 : False := by grind
  exact eq119035
