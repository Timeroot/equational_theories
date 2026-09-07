import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3716`: `x ◇ y = (x ◇ x) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if X = Y then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_x_y_pxy_pxx_x_Equation3716 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law3716 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3716.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ a = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1 x
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 (M.op x x) X1
       have r₂ := eq9 x x x
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq37
    | exact resolve eq37 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq37
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq172 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq188 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq172 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq172
    | (have j0 := eq172 X0
       grind)
    | exact resolve eq172 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq172
  have eq189 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq188 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq188
    | (have j0 := eq188 X0
       grind)
    | exact resolve eq188 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq190 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq189 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq189 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq189 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq491 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X0 X1
       have i₂ := eq190 (σ X0)
       grind)
    | exact superpose eq190 eq22
    | exact resolve eq22 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq525 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k (k (τ (σ X0)) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq491 X0 X1
       have i₂ := eq39 (σ X0) (σ X1)
       grind)
    | exact superpose eq39 eq491
    | exact resolve eq491 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq533 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq525
    | exact resolve eq525 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq538 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq533 X0 X1
       have i₂ := eq190 X0
       grind)
    | exact superpose eq190 eq533
    | exact resolve eq533 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq533
  have eq540 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq538
    | exact resolve eq538 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq538
  have eq555 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq540 x y
       grind)
    | exact superpose eq540 eq16
    | (have r₁ := eq16
       have r₂ := eq540 x y
       grind)
    | exact resolve eq16 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq568 : False := by grind
  exact eq568

/-- `Equation3716`: `x ◇ y = (x ◇ x) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if X = Y then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_x_y_pxy_pxy_x_Equation3716 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law3716 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3716.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ a = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1 x
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 (M.op x x) X1
       have r₂ := eq9 x x x
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq37
    | exact resolve eq37 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq37
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq172 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq188 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq172 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq172
    | (have j0 := eq172 X0
       grind)
    | exact resolve eq172 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq172
  have eq189 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq188 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq188
    | (have j0 := eq188 X0
       grind)
    | exact resolve eq188 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq190 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq189 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq189 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq189 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq491 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X0 X1
       have i₂ := eq190 (σ X0)
       grind)
    | exact superpose eq190 eq22
    | exact resolve eq22 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq525 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k (k (τ (σ X0)) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq491 X0 X1
       have i₂ := eq39 (σ X0) (σ X1)
       grind)
    | exact superpose eq39 eq491
    | exact resolve eq491 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq533 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq525
    | exact resolve eq525 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq538 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq533 X0 X1
       have i₂ := eq190 X0
       grind)
    | exact superpose eq190 eq533
    | exact resolve eq533 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq533
  have eq540 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq538
    | exact resolve eq538 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq538
  have eq555 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq540 x y
       grind)
    | exact superpose eq540 eq16
    | (have r₁ := eq16
       have r₂ := eq540 x y
       grind)
    | exact resolve eq16 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq568 : False := by grind
  exact eq568

/-- `Equation3716`: `x ◇ y = (x ◇ x) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_pxy_x_Equation3716 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law3716 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3716.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1 x
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq48 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq27 X0 (M.op X1 X2)
       grind)
    | exact superpose eq27 eq9
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq13 (M.op x x) X1
       have r₂ := eq9 x x x
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq63
    | (have j0 := eq63 X0 X1
       grind)
    | exact resolve eq63 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq63
  have eq119 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq48
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (k (σ (M.op X0 X0)) X1) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq66
    | exact resolve eq66 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (M.op X0 X0)
       have i₂ := eq66 X0 (τ X1)
       grind)
    | exact superpose eq66 eq19
    | (have j1 := eq66 X0 (τ X1)
       grind)
    | exact resolve eq19 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq66
  have eq2692 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (σ (M.op X0 X0)) = X1 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1
       have i₂ := eq145 X0 X1
       grind)
    | exact superpose eq145 eq141
    | (have j0 := eq141 X0 X1
       have j1 := eq145 X0 X1
       grind)
    | exact resolve eq141 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq145
  have eq73101 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (σ (M.op X1 (τ X0))) = (M.op (σ X1) X0) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq2692 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq2692 X0 (σ X0)
       grind)
    | exact superpose eq2692 eq10
    | (have j1 := eq2692 X1 X0
       grind)
    | exact resolve eq10 eq2692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2692
  have eq73512 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (σ (M.op X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq73101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73101
  have eq79891 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq73512 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73512
    | exact resolve eq73512 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73512
  have eq82525 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79891 y x
       grind)
    | exact superpose eq79891 eq16
    | (have j1 := eq79891 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq79891 y x
       grind)
    | exact resolve eq16 eq79891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79891
  have eq82939 : y = (M.op x x) := by grind
  clear eq82525
  have eq84335 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq119 x X0
       have i₂ := eq82939
       grind)
    | exact superpose eq82939 eq119
    | exact resolve eq119 eq82939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq84413 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq48 X0 x x
       have i₂ := eq82939
       grind)
    | exact superpose eq82939 eq48
    | exact resolve eq48 eq82939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq91056 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84335 (σ x)
       grind)
    | exact superpose eq84335 eq16
    | exact resolve eq16 eq84335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84335
  have eq91098 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq91056
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq91056
    | exact resolve eq91056 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq91056
  have eq91241 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq91098
       have i₂ := eq82939
       grind)
    | exact superpose eq82939 eq91098
    | exact resolve eq91098 eq82939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91098
  have eq91352 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq91241
       have i₂ := eq84413 x
       grind)
    | exact superpose eq84413 eq91241
    | exact resolve eq91241 eq84413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84413 eq91241
  have eq91414 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq91352
       have i₂ := eq82939
       grind)
    | exact superpose eq82939 eq91352
    | exact resolve eq91352 eq82939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82939 eq91352
  have eq91415 : False := by grind
  exact eq91415

/-- `Equation3748`: `x ◇ y = (y ◇ x) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_y_pxy_Equation3748 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3748 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3748.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
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
  have eq77 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq81 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 (M.op (M.op X1 X0) (M.op X0 X0)) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 (M.op X1 X1)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq133 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq93 (σ X1) (σ X0)
       grind)
    | exact superpose eq93 eq15
    | (have j1 := eq93 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq93 X1 (τ X0)
       grind)
    | exact superpose eq93 eq19
    | (have j1 := eq93 X1 (τ X0)
       grind)
    | exact resolve eq19 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq141 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq93
  have eq323 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq532 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq141 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq533 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq588 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq533 (σ X0)
       grind)
    | exact superpose eq533 eq15
    | exact resolve eq15 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq588 X0
       have i₂ := eq533 X0
       grind)
    | exact superpose eq533 eq588
    | exact resolve eq588 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq588
  have eq884 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq595 X0
       grind)
    | exact superpose eq595 eq9
    | exact resolve eq9 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1166 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 (M.op X0 X0)
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq85
    | (have j0 := eq85 X1 X0
       grind)
    | exact resolve eq85 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1266 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1166 X0 X1
       have j1 := eq323 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq1166 X0 X1
       have r₂ := eq323 (M.op X0 X0) (M.op X1 X1)
       grind)
    | (have r₁ := eq1166 X0 X1
       have r₂ := eq323 (M.op X1 X1) (M.op X0 X0)
       grind)
    | (have r₁ := eq1166 X0 X1
       have r₂ := eq323 (M.op X1 (M.op X0 X0)) (k X1 (M.op X0 X0))
       grind)
    | exact resolve eq1166 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq1166
  have eq4222 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq135 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq135
    | exact resolve eq135 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq4405 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4222 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4222
    | (have j0 := eq4222 X0 X1
       grind)
    | exact resolve eq4222 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4222
  have eq8288 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq133 X1 X0
       grind)
    | exact superpose eq133 eq10
    | (have j1 := eq133 X1 X0
       grind)
    | exact resolve eq10 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq8475 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8288 X0 X1
       have i₂ := eq595 X0
       grind)
    | exact superpose eq595 eq8288
    | (have j0 := eq8288 X0 X1
       grind)
    | exact resolve eq8288 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8288
  have eq8620 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8475 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq8475
    | (have j0 := eq8475 X0 X1
       grind)
    | exact resolve eq8475 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8475
  have eq10310 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  clear eq1266
  have eq10426 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq10310 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10310
  have eq10498 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10426 (σ X0) X1
       have i₂ := eq595 X0
       grind)
    | exact superpose eq595 eq10426
    | exact resolve eq10426 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq10801 : ∀ X0 X1 : G, (σ (k X0 (M.op X1 X1))) = (M.op (σ X0) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (M.op X1 X1)
       have i₂ := eq10498 X1 (σ X0)
       grind)
    | exact superpose eq10498 eq15
    | exact resolve eq15 eq10498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10498
  have eq10824 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X1 X1))) = (σ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10801 X0 X1
       have i₂ := eq10426 X1 X0
       grind)
    | exact superpose eq10426 eq10801
    | exact resolve eq10801 eq10426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10426 eq10801
  have eq14603 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X0)) = (M.op (σ (M.op X0 (M.op X1 X1))) (σ (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq884 (M.op X1 X1) (σ X0)
       have i₂ := eq10824 X0 X1
       grind)
    | exact superpose eq10824 eq884
    | exact resolve eq884 eq10824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq14732 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X0)) = (σ (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14603 X0 X1
       have i₂ := eq10824 (M.op X0 (M.op X1 X1)) (M.op X1 X1)
       grind)
    | exact superpose eq10824 eq14603
    | exact resolve eq14603 eq10824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10824 eq14603
  have eq14779 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X0)) = (σ (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14732 X0 X1
       have i₂ := eq9 (M.op X1 X1) X0
       grind)
    | exact superpose eq9 eq14732
    | exact resolve eq14732 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14732
  have eq136948 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8620 y x
       grind)
    | exact superpose eq8620 eq16
    | (have j1 := eq8620 y x
       grind)
    | exact resolve eq16 eq8620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8620
  have eq137466 : x = (M.op y y) := by
    first
    | (have j1 := eq4405 x y
       grind)
    | (have r₁ := eq136948
       have r₂ := eq4405 x y
       grind)
    | exact resolve eq136948 eq4405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4405 eq136948
  have eq139559 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14779 X0 y
       have i₂ := eq137466
       grind)
    | exact superpose eq137466 eq14779
    | exact resolve eq14779 eq137466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14779 eq137466
  have eq149890 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq139559 y
       grind)
    | exact superpose eq139559 eq16
    | (have r₁ := eq16
       have r₂ := eq139559 y
       grind)
    | exact resolve eq16 eq139559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139559
  have eq150020 : False := by grind
  exact eq150020

/-- `Equation3748`: `x ◇ y = (y ◇ x) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_y_pyx_Equation3748 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3748 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3748.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq36 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq38 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq36
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq77 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq89 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq154 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (M.op (M.op (M.op X0 X1) (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq27 X0 X1
       grind)
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X1)
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq9
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq26 X0 X0
       have i₂ := eq27 X0 (M.op X0 X0)
       grind)
    | exact superpose eq27 eq26
    | exact resolve eq26 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq160 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq154 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq154
    | exact resolve eq154 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq682 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq77
  have eq748 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq27 (M.op X0 X0) (M.op (M.op X0 X0) X0)
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq27
    | exact resolve eq27 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq748 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq748
    | exact resolve eq748 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq755 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq753 X0
       have i₂ := eq9 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq753
    | exact resolve eq753 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq1732 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq87 X1 X0
       grind)
    | exact superpose eq87 eq10
    | (have j1 := eq87 X1 X0
       grind)
    | exact resolve eq10 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1835 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq87 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq1836 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1835 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1986 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1836 (M.op X0 X0)
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq1836
    | (have j0 := eq1836 (M.op X0 X0)
       grind)
    | exact resolve eq1836 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1836
  have eq1993 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1986 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986
  have eq4197 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) (M.op X0 X0)
       have i₂ := eq755 X0
       grind)
    | exact superpose eq755 eq9
    | exact resolve eq9 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq4208 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq4197 X0
       have i₂ := eq27 X0 (M.op X0 X0)
       grind)
    | exact superpose eq27 eq4197
    | exact resolve eq4197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4197
  have eq4215 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq4208 X0
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq4208
    | exact resolve eq4208 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq4208
  have eq23504 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq682 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq23506 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23504 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23504
  have eq23507 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23506 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23506
  have eq23833 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23507 (σ X0)
       grind)
    | exact superpose eq23507 eq15
    | exact resolve eq15 eq23507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23852 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23833 X0
       have i₂ := eq23507 X0
       grind)
    | exact superpose eq23507 eq23833
    | exact resolve eq23833 eq23507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23507 eq23833
  have eq25597 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq23852 X0
       grind)
    | exact superpose eq23852 eq9
    | exact resolve eq9 eq23852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25600 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq25762 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25600 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq25600
    | exact resolve eq25600 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25600
  have eq25812 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq25762
  have eq28461 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq160 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq25812 X0
       grind)
    | exact superpose eq25812 eq160
    | exact resolve eq160 eq25812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq28484 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq28461 X0
       have i₂ := eq23852 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23852 eq28461
    | exact resolve eq28461 eq23852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28461
  have eq28531 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ (M.op X0 X0))) (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq28484 X0
       have i₂ := eq1993 X0
       grind)
    | exact superpose eq1993 eq28484
    | exact resolve eq28484 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993 eq28484
  have eq28552 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq28531 X0
       have i₂ := eq25597 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq25597 eq28531
    | exact resolve eq28531 eq25597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25597 eq28531
  have eq28561 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq28552 X0
       have i₂ := eq25812 X0
       grind)
    | exact superpose eq25812 eq28552
    | exact resolve eq28552 eq25812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28552
  have eq28566 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq28561 X0
       have i₂ := eq25812 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq25812 eq28561
    | exact resolve eq28561 eq25812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28561
  have eq28571 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq28566 X0
       have i₂ := eq4215 X0
       grind)
    | exact superpose eq4215 eq28566
    | exact resolve eq28566 eq4215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4215 eq28566
  have eq40804 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq41640 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40804 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq40804
    | (have j0 := eq40804 X0 X1
       grind)
    | exact resolve eq40804 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40804
  have eq175037 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq1732 X1 X0
       grind)
    | exact superpose eq1732 eq10
    | (have j1 := eq1732 X1 X0
       grind)
    | exact resolve eq10 eq1732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732
  have eq175409 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq175037 X0 X1
       have i₂ := eq23852 X0
       grind)
    | exact superpose eq23852 eq175037
    | (have j0 := eq175037 X0 X1
       grind)
    | exact resolve eq175037 eq23852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175037
  have eq175449 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq175409 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq175409
    | (have j0 := eq175409 X0 X1
       grind)
    | exact resolve eq175409 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175409
  have eq175484 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq175449 X0 X1
       have i₂ := eq23852 X1
       grind)
    | exact superpose eq23852 eq175449
    | (have j0 := eq175449 X0 X1
       grind)
    | exact resolve eq175449 eq23852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23852 eq175449
  have eq175507 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq175484 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq175484
    | (have j0 := eq175484 X0 X1
       grind)
    | exact resolve eq175484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175484
  have eq446411 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq175507 x y
       grind)
    | exact superpose eq175507 eq16
    | (have j1 := eq175507 x y
       grind)
    | exact resolve eq16 eq175507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175507
  have eq446441 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq41640 x y
       grind)
    | (have r₁ := eq446411
       have r₂ := eq41640 y x
       grind)
    | exact resolve eq446411 eq41640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41640 eq446411
  have eq450089 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq28571 y
       have i₂ := eq446441
       grind)
    | exact superpose eq446441 eq28571
    | exact resolve eq28571 eq446441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28571 eq446441
  have eq450244 : y = (M.op x x) := by
    first
    | (have r₁ := eq450089
       have r₂ := eq16
       grind)
    | exact resolve eq450089 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450089
  have eq450991 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25812 x
       have i₂ := eq450244
       grind)
    | exact superpose eq450244 eq25812
    | exact resolve eq25812 eq450244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25812 eq450244
  have eq451194 : False := by grind
  exact eq451194

/-- `Equation3748`: `x ◇ y = (y ◇ x) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pxy_y_pxy_Equation3748 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3748 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3748.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq9 X1 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq72 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X2 X1) X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq76 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X2 X1) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq72 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq72 (M.op X1 X2) X1 X2
       have r₂ := eq12 (M.op X2 X1) (M.op X1 X2)
       grind)
    | (have r₁ := eq72 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq72 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq77 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq74 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq74 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq78 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq70 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq70 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq70 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq77
    | exact resolve eq77 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq120 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq78 X0 (τ X1)
       grind)
    | exact superpose eq78 eq19
    | (have j1 := eq78 X0 X1
       grind)
    | exact resolve eq19 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq122 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq78 (σ X0) (σ X1)
       grind)
    | exact superpose eq78 eq15
    | (have j1 := eq78 (σ X0) X1
       grind)
    | exact resolve eq15 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) = (M.op (M.op X1 X2) X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq26 X0 X1
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq26
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (M.op (M.op (M.op X0 X1) (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq26 X0 X1
       grind)
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X1)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq25 X0 X0
       have i₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact superpose eq26 eq25
    | exact resolve eq25 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq240 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq232 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq232
    | exact resolve eq232 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq241 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) = (M.op (M.op X1 X2) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq228 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq228 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq228 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq559 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq660 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq66 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq662 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq660 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq1007 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq120 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120
    | (have j0 := eq120 X1 X1
       grind)
    | exact resolve eq120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq1068 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1007 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1007
    | (have j0 := eq1007 X0 X1
       grind)
    | exact resolve eq1007 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1075 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq233 X0
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq233
    | (have j1 := eq78 X0 X1
       grind)
    | exact resolve eq233 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq1190 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq662 (M.op X0 X0)
       have i₂ := eq559 X0
       grind)
    | exact superpose eq559 eq662
    | (have j0 := eq662 (M.op X0 X0)
       grind)
    | exact resolve eq662 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq662
  have eq1203 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1190 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1360 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1203 X1
       have i₂ := eq1068 X0 X1
       grind)
    | exact superpose eq1068 eq1203
    | (have j1 := eq1068 X1 X0
       grind)
    | exact resolve eq1203 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068 eq1203
  have eq2080 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq122 x y
       grind)
    | exact superpose eq122 eq16
    | (have j1 := eq122 x x
       grind)
    | exact resolve eq16 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq2144 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq1360 x x
       grind)
    | (have r₁ := eq2080
       have r₂ := eq1360 x y
       grind)
    | exact resolve eq2080 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360 eq2080
  have eq2155 : (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq95 x x
       have i₂ := eq2144
       grind)
    | exact superpose eq2144 eq95
    | (have j0 := eq95 x x
       grind)
    | exact resolve eq95 eq2144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq2160 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq25 (σ x) x
       have i₂ := eq2144
       grind)
    | exact superpose eq2144 eq25
    | exact resolve eq25 eq2144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2176 : (σ x) = (σ (k x x)) := by grind
  clear eq2155
  have eq2299 : (k x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq2176
       grind)
    | exact superpose eq2176 eq10
    | exact resolve eq10 eq2176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176
  have eq2340 : x = (k x x) := by
    first
    | (have i₁ := eq2299
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2299
    | exact resolve eq2299 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2299
  have eq2411 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq78 x x
       have i₂ := eq2340
       grind)
    | exact superpose eq2340 eq78
    | (have j0 := eq78 x x
       grind)
    | exact resolve eq78 eq2340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq2340
  have eq2416 : x = (M.op x x) := by grind
  clear eq2411
  have eq2480 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | (have i₁ := eq25 x x
       have i₂ := eq2416
       grind)
    | exact superpose eq2416 eq25
    | exact resolve eq25 eq2416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq2610 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X1 X2)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 X0 X1 X2
       have i₂ := eq241 X0 X2 X1
       grind)
    | (have i₁ := eq76 (M.op X2 X1) X1 X2
       have i₂ := eq241 (M.op X2 X1) X1 X2
       grind)
    | exact superpose eq241 eq76
    | (have j0 := eq76 X0 X1 X2
       have j1 := eq241 X0 X1 X2
       grind)
    | exact resolve eq76 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq241
  have eq2826 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq240 X1 X1
       have i₂ := eq14 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq240 X0 X1
       have i₂ := eq14 (M.op (M.op X0 X1) (M.op X0 X0)) X1
       grind)
    | exact superpose eq14 eq240
    | (have j1 := eq14 X0 (M.op X1 X1)
       grind)
    | exact resolve eq240 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq2949 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2826 X0 X1
       have j1 := eq12 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq2826 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq2826 X0 (M.op X0 X0)
       have r₂ := eq12 (M.op X0 X0) (M.op X0 X0)
       grind)
    | (have r₁ := eq2826 X0 X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq2826 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826
  have eq51357 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq2949 X0 x
       have i₂ := eq2416
       grind)
    | exact superpose eq2416 eq2949
    | exact resolve eq2949 eq2416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416 eq2949
  have eq52312 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1075 X0 X1
       have i₂ := eq51357 X0
       grind)
    | exact superpose eq51357 eq1075
    | (have j0 := eq1075 X0 X1
       have j1 := eq51357 X0
       grind)
    | exact resolve eq1075 eq51357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075 eq51357
  have eq52571 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have j0 := eq52312 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq52312 X0 X1
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq52312 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52312
  have eq73418 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq52571 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52571
  have eq73419 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq73418 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73418
  have eq166355 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2610 X0 (σ x) (σ x)
       have i₂ := eq2144
       grind)
    | exact superpose eq2144 eq2610
    | (have j0 := eq2610 X0 (σ x) (σ x)
       grind)
    | exact resolve eq2610 eq2144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2144 eq2610
  have eq166368 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq166355 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166355
  have eq166369 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq166368 X0
       have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq166368 X0
       have r₂ := eq12 X0 (σ x)
       grind)
    | exact resolve eq166368 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166368
  have eq166477 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq166369 (σ X0)
       grind)
    | exact superpose eq166369 eq15
    | exact resolve eq15 eq166369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166369
  have eq166561 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq166477 X0
       have i₂ := eq73419 X0
       grind)
    | exact superpose eq73419 eq166477
    | exact resolve eq166477 eq73419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73419 eq166477
  have eq166965 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (M.op (σ (M.op X0 x)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2160 (σ X0)
       have i₂ := eq166561 X0
       grind)
    | exact superpose eq166561 eq2160
    | exact resolve eq2160 eq166561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160
  have eq167117 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq166965 X0
       have i₂ := eq166561 (M.op X0 x)
       grind)
    | exact superpose eq166561 eq166965
    | exact resolve eq166965 eq166561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166561 eq166965
  have eq167230 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq167117 X0
       have i₂ := eq2480 X0
       grind)
    | exact superpose eq2480 eq167117
    | exact resolve eq167117 eq2480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480 eq167117
  have eq168137 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq167230 y
       grind)
    | exact superpose eq167230 eq16
    | (have r₁ := eq16
       have r₂ := eq167230 y
       grind)
    | exact resolve eq16 eq167230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167230
  have eq168306 : False := by grind
  exact eq168306

/-- `Equation3756`: `x ◇ y = (y ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_x_pyx_Equation3756 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3756 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3756.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op X1 X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 X1 X2 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 (M.op x x) X1
       have r₂ := eq9 x x x
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq68 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X2 X1) X0) ∨ (M.op X3 X3) = X3 ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq14 X3 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 (M.op X2 X2)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X3 X3
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq78 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq78 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq78 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq78 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq81 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X2 X1) X0) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq70 X0 X1 X2 X3
       have j1 := eq12 X3 X0
       grind)
    | (have r₁ := eq70 (M.op X1 X1) X1 X1 X3
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq70 X0 X1 X2 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq70 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq83 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq68 (M.op X0 X0) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq68 X0 (M.op X0 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq68 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq68 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       have j1 := eq80 X1 X0
       grind)
    | (have r₁ := eq83 X0 X1
       have r₂ := eq80 (k X1 X0) X1
       grind)
    | (have r₁ := eq83 X0 X0
       have r₂ := eq80 X0 (k X0 X0)
       grind)
    | (have r₁ := eq83 X0 X1
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq83 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq80 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq101 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0 X1
       have i₂ := eq26 X1 X1 X0
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq90 (σ X0)
       grind)
    | exact superpose eq90 eq15
    | exact resolve eq15 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq90 (τ X0)
       grind)
    | exact superpose eq90 eq19
    | exact resolve eq19 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq114
    | exact resolve eq114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq119 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq110
    | exact resolve eq110 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq121 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq115 X0
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq115
    | exact resolve eq115 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq115
  have eq129 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq36 X0 X1
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq36
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq36 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = (τ (M.op (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op X1 X1) X0
       have i₂ := eq36 X1 (σ X0)
       grind)
    | exact superpose eq36 eq23
    | exact resolve eq23 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = (σ (M.op (τ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (M.op X1 X1)
       have i₂ := eq36 X1 (τ X0)
       grind)
    | exact superpose eq36 eq19
    | exact resolve eq19 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq129 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq129 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq129 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq146 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq101 X0 X1
       have i₂ := eq14 X0 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq101
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq101 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X1) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq101 X1 X0
       grind)
    | (have i₁ := eq12 X1 X2
       have i₂ := eq101 X0 X1
       grind)
    | exact superpose eq101 eq12
    | (have j0 := eq12 X1 X2
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq101 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq101 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq171 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq146 X0 X1 X2
       have j1 := eq162 X0 X2 X0
       grind)
    | (have r₁ := eq146 X1 X0 X2
       have r₂ := eq162 X0 X1 X2
       grind)
    | (have r₁ := eq146 (M.op X0 X0) X1 X2
       have r₂ := eq162 X0 (M.op X1 X1) X2
       grind)
    | (have r₁ := eq146 X0 X1 X1
       have r₂ := eq162 X1 X1 X2
       grind)
    | exact resolve eq146 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq174 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq87
    | exact resolve eq87 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq87 (τ X0) X1
       grind)
    | exact superpose eq87 eq19
    | (have j1 := eq87 (τ X0) X1
       grind)
    | exact resolve eq19 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq181 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq87 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq269 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (σ X0) X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq36
    | exact resolve eq36 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X1 (σ X0)
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq101
    | exact resolve eq101 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq308 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X1)) = (k (M.op X0 X1) X2) ∨ (M.op (M.op X1 X0) X3) = (k X3 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq36 (M.op X2 X1) X1
       have i₂ := eq81 (M.op X2 X1) X1 X2 X3
       grind)
    | exact superpose eq81 eq36
    | (have j1 := eq81 X2 X1 X2 (M.op X0 X1)
       grind)
    | exact resolve eq36 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq339 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq272 X2 X1
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq272 X0 X1
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq272
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq272 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 X2 : G, (k (τ X1) (M.op X2 X2)) = (τ (k X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op X2 X2)
       have i₂ := eq272 X2 X0
       grind)
    | exact superpose eq272 eq23
    | exact resolve eq23 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq367 : ∀ X0 X1 X2 : G, (σ (k (M.op X1 X1) X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (M.op X1 X1) X2
       have i₂ := eq272 X1 X0
       grind)
    | exact superpose eq272 eq15
    | exact resolve eq15 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq272 X1 X0
       grind)
    | exact superpose eq272 eq10
    | exact resolve eq10 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq369 : ∀ X0 X1 X2 : G, (σ (k (M.op X1 X1) X2)) = (M.op (σ X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq367 X0 X1 X2
       have i₂ := eq36 X0 (σ X2)
       grind)
    | exact superpose eq36 eq367
    | exact resolve eq367 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq374 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq339 X0 X1 X2
       have j1 := eq162 X0 X2 X0
       grind)
    | (have r₁ := eq339 X0 X0 X2
       have r₂ := eq162 X0 (σ X0) X2
       grind)
    | (have r₁ := eq339 X0 X1 X1
       have r₂ := eq162 X1 X1 X2
       grind)
    | (have r₁ := eq339 X0 X1 (M.op X0 X0)
       have r₂ := eq162 X0 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       grind)
    | exact resolve eq339 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq376 : ∀ X0 X1 X2 : G, (M.op (σ X2) (M.op X0 X0)) = (σ (M.op X2 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq369 X0 X1 X2
       have i₂ := eq36 X1 X2
       grind)
    | exact superpose eq36 eq369
    | exact resolve eq369 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq428 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X2 X1) (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 x
       have i₂ := eq368 X0 x
       grind)
    | exact superpose eq368 eq9
    | exact resolve eq9 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 X1
       have i₂ := eq368 X0 X1
       grind)
    | exact superpose eq368 eq36
    | exact resolve eq36 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1043 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ X1) ∨ (σ (k X2 X1)) = (M.op (σ X1) (σ X2)) ∨ (M.op X0 X0) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq101 (σ X1) X1
       grind)
    | (have i₁ := eq72 X0 X1
       have i₂ := eq101 X0 (σ X1)
       grind)
    | exact superpose eq101 eq72
    | (have j0 := eq72 X1 X2
       grind)
    | exact resolve eq72 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq101
  have eq1838 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq135 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq135 eq15
    | (have j1 := eq135 (σ X0) X2 X2
       grind)
    | exact resolve eq15 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq3151 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq177
    | exact resolve eq177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq3246 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3151 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3151
    | (have j0 := eq3151 X0 X1
       grind)
    | exact resolve eq3151 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3151
  have eq3488 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq174 y x
       grind)
    | exact superpose eq174 eq16
    | (have j1 := eq174 y x
       grind)
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq12800 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X1)) ≠ (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (k (M.op X0 X1) (M.op X1 X0)) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq308 X0 X1 (M.op X1 X0) (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq12801 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X1 X0)) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq12800 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12800
  have eq32461 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X2 X2))) = (k (τ (σ X0)) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X0 (M.op X2 X2)
       have i₂ := eq365 X2 (σ X0) X1
       grind)
    | exact superpose eq365 eq32
    | exact resolve eq32 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32462 : ∀ X0 X1 X2 : G, (k X0 (M.op X2 X2)) = (σ (k (τ X0) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (M.op X2 X2))
       have i₂ := eq365 X2 X0 X1
       grind)
    | exact superpose eq365 eq11
    | exact resolve eq11 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq32503 : ∀ X0 X1 X2 : G, (k X0 (M.op X2 X2)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32462 X0 X1 X2
       have i₂ := eq18 X0 (M.op X1 X1)
       grind)
    | exact superpose eq18 eq32462
    | exact resolve eq32462 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq32462
  have eq32504 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = (k X0 (τ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32461 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32461
    | exact resolve eq32461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32461
  have eq34317 : ∀ X0 X1 X2 : G, (k X0 (M.op X2 X2)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32503 X0 x X2
       have i₂ := eq32503 X0 x X1
       grind)
    | exact superpose eq32503 eq32503
    | exact resolve eq32503 eq32503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32503
  have eq35009 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = X0 ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165 X2 X0
       have i₂ := eq34317 X0 X1 X2
       grind)
    | (have i₁ := eq165 X2 X0
       have i₂ := eq34317 X0 X2 X1
       grind)
    | exact superpose eq34317 eq165
    | (have j0 := eq165 X1 X0
       grind)
    | exact resolve eq165 eq34317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq34317
  have eq38333 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X2) X0) = X0 ∨ (k X0 (M.op X3 X3)) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq26 X2 X2 X2
       have i₂ := eq35009 X0 x X2
       grind)
    | (have i₁ := eq26 X0 x X2
       have i₂ := eq35009 (M.op x X0) x X2
       grind)
    | exact superpose eq35009 eq26
    | (have j1 := eq35009 X0 X3 X2
       grind)
    | exact resolve eq26 eq35009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq35009
  have eq45851 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X1 X0)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq376 X2 x (M.op X1 X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq376
    | exact resolve eq376 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46018 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op X1 X1)) = (k (σ (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134 X0 X2
       have i₂ := eq376 X1 X2 (τ X0)
       grind)
    | exact superpose eq376 eq134
    | exact resolve eq134 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq46111 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (k (σ (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46018 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46018
    | exact resolve eq46018 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46018
  have eq48128 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46111 X1 X2 (τ X0)
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq46111
    | exact resolve eq46111 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq48392 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X1) = (M.op (k (σ (M.op X0 X0)) X1) (τ (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq428 X3 (M.op X2 X2) X1
       have i₂ := eq46111 X1 X2 X0
       grind)
    | exact superpose eq46111 eq428
    | exact resolve eq428 eq46111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46111
  have eq48561 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X1) = (M.op (M.op X1 (σ (M.op X0 X0))) (τ (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq48392 X0 X1 X2 X3
       have i₂ := eq269 X0 X1
       grind)
    | exact superpose eq269 eq48392
    | exact resolve eq48392 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48392
  have eq48889 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48561 X0 X1 X2 x
       have i₂ := eq428 x (σ (M.op X0 X0)) X1
       grind)
    | exact superpose eq428 eq48561
    | exact resolve eq48561 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48561
  have eq51021 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X1) = (M.op (k (M.op X0 X0) X1) (τ (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq428 X3 (M.op X2 X2) X1
       have i₂ := eq48128 X0 X1 X2
       grind)
    | exact superpose eq48128 eq428
    | exact resolve eq428 eq48128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48128
  have eq51091 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X1) = (M.op (M.op X1 (M.op X0 X0)) (τ (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51021 X0 X1 X2 X3
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq51021
    | exact resolve eq51021 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq51021
  have eq51390 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51091 X2 X1 X0 x
       have i₂ := eq428 x (M.op X2 X2) X1
       grind)
    | exact superpose eq428 eq51091
    | exact resolve eq51091 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51091
  have eq59372 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ X1 ∨ (k X1 (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X1 (M.op X2 X2)
       have i₂ := eq51390 X2 X1 X0
       grind)
    | (have i₁ := eq181 X1 (M.op X2 X2)
       have i₂ := eq51390 X0 X1 X2
       grind)
    | exact superpose eq51390 eq181
    | (have j0 := eq181 X1 (M.op X0 X0)
       grind)
    | exact resolve eq181 eq51390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51390
  have eq59444 : ∀ X1 X2 : G, (k X1 (M.op X2 X2)) = X1 := by
    intro X1 X2
    first
    | (have j0 := eq59372 x X1 X2
       have j1 := eq38333 X1 X2 X2
       grind)
    | (have r₁ := eq59372 X2 x X2
       have r₂ := eq38333 x X2 x
       grind)
    | exact resolve eq59372 eq38333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38333 eq59372
  have eq61761 : ∀ X0 X2 : G, (k X0 (τ (M.op X2 X2))) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq32504 X0 x X2
       have i₂ := eq59444 X0 x
       grind)
    | exact superpose eq59444 eq32504
    | exact resolve eq32504 eq59444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32504 eq59444
  have eq75641 : ∀ X0 X1 X2 : G, (k (τ (M.op X2 X2)) (M.op (τ X1) (M.op X0 X0))) = (τ (M.op (k (σ (M.op X0 X0)) X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq133 (M.op (τ X1) (M.op X0 X0)) X2
       have i₂ := eq134 X1 X0
       grind)
    | exact superpose eq134 eq133
    | exact resolve eq133 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq134
  have eq75988 : ∀ X0 X1 X2 : G, (k (τ (M.op X2 X2)) (M.op (τ X1) (M.op X0 X0))) = (τ (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75641 X0 X1 X2
       have i₂ := eq269 X0 X1
       grind)
    | exact superpose eq269 eq75641
    | exact resolve eq75641 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75641
  have eq76151 : ∀ X0 X1 X2 : G, (k (τ (M.op X2 X2)) (M.op (τ X1) (M.op X0 X0))) = (τ (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75988 X0 X1 X2
       have i₂ := eq9 (σ (M.op X0 X0)) X1 X2
       grind)
    | exact superpose eq9 eq75988
    | exact resolve eq75988 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75988
  have eq76262 : ∀ X0 X1 X2 : G, (τ (M.op (σ (M.op X0 X0)) X1)) = (M.op (M.op (τ X1) (M.op X0 X0)) (τ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76151 X0 X1 X2
       have i₂ := eq434 X2 (M.op (τ X1) (M.op X0 X0))
       grind)
    | exact superpose eq434 eq76151
    | exact resolve eq76151 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434 eq76151
  have eq76325 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ X1)) = (τ (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76262 X0 X1 x
       have i₂ := eq428 x (M.op X0 X0) (τ X1)
       grind)
    | exact superpose eq428 eq76262
    | exact resolve eq76262 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq76262
  have eq97132 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq3488
       have i₂ := eq171 x x y
       grind)
    | exact superpose eq171 eq3488
    | (have j1 := eq171 x X0 x
       grind)
    | exact resolve eq3488 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97135 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq3488
       have i₂ := eq374 x x y
       grind)
    | exact superpose eq374 eq3488
    | (have j1 := eq374 x X0 x
       grind)
    | exact resolve eq3488 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq97137 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq3488
       have i₂ := eq3246 x y
       grind)
    | exact superpose eq3246 eq3488
    | (have j1 := eq3246 x y
       grind)
    | (have r₁ := eq3488
       have r₂ := eq3246 x y
       grind)
    | exact resolve eq3488 eq3246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3246 eq3488
  have eq97149 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
  clear eq97137
  have eq97151 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq97135 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97135
  have eq97154 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq97132 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97132
  have eq97175 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq97149
       grind)
    | exact superpose eq97149 eq10
    | exact resolve eq10 eq97149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97149
  have eq97308 : y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq97175
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq97175
    | exact resolve eq97175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97175
  have eq97315 : y = (k y x) := by
    first
    | (have j1 := eq181 y x
       grind)
    | (have r₁ := eq97308
       have r₂ := eq181 y x
       grind)
    | exact resolve eq97308 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq97308
  have eq98131 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq171 x X0 y
       have i₂ := eq97315
       grind)
    | exact superpose eq97315 eq171
    | (have j0 := eq171 x X0 x
       grind)
    | exact resolve eq171 eq97315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq118719 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq269 X0 x
       have i₂ := eq97154 X0
       grind)
    | exact superpose eq97154 eq269
    | exact resolve eq269 eq97154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq97154
  have eq146281 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1838 x y X0
       grind)
    | exact superpose eq1838 eq16
    | (have j1 := eq1838 x x X0
       grind)
    | exact resolve eq16 eq1838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838
  have eq146949 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq146281 X0
       have i₂ := eq97315
       grind)
    | exact superpose eq97315 eq146281
    | (have j0 := eq146281 X0
       grind)
    | exact resolve eq146281 eq97315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146281
  have eq147177 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq146949 X0
       have j1 := eq118719 X0
       grind)
    | (have r₁ := eq146949 X0
       have r₂ := eq118719 X0
       grind)
    | exact resolve eq146949 eq118719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118719 eq146949
  have eq147256 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq32 x X0
       have i₂ := eq147177 X0
       grind)
    | exact superpose eq147177 eq32
    | exact resolve eq32 eq147177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq147263 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq147177 (σ X0)
       grind)
    | exact superpose eq147177 eq15
    | exact resolve eq15 eq147177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147177
  have eq150202 : ∀ X0 X1 : G, (k x (τ (M.op X1 X1))) = (τ (M.op (σ (M.op X0 X0)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq147256 (M.op X1 X1)
       have i₂ := eq48889 X0 (σ x) X1
       grind)
    | exact superpose eq48889 eq147256
    | exact resolve eq147256 eq48889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48889 eq147256
  have eq150520 : ∀ X0 X1 : G, (k x (τ (M.op X1 X1))) = (M.op (M.op X0 X0) (τ (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq150202 X0 X1
       have i₂ := eq76325 X0 (σ x)
       grind)
    | exact superpose eq76325 eq150202
    | exact resolve eq150202 eq76325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76325 eq150202
  have eq150616 : ∀ X0 X1 : G, (M.op (M.op X0 X0) x) = (k x (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq150520 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq150520
    | exact resolve eq150520 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150520
  have eq150631 : ∀ X0 : G, x = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | (have i₁ := eq150616 X0 x
       have i₂ := eq61761 x x
       grind)
    | exact superpose eq61761 eq150616
    | exact resolve eq150616 eq61761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61761 eq150616
  have eq159244 : ∀ X0 X1 : G, (M.op (σ x) (σ X0)) = (M.op (σ (k x X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ x) (σ X0) X1
       have i₂ := eq147263 X0
       grind)
    | exact superpose eq147263 eq9
    | exact resolve eq9 eq147263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147263
  have eq234762 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 X0) = (σ x) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1043 X0 x y
       grind)
    | exact superpose eq1043 eq16
    | (have j1 := eq1043 X0 x x
       grind)
    | exact resolve eq16 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq234817 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op X0 X0) = (σ x) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq234762 X0
       have i₂ := eq97315
       grind)
    | exact superpose eq97315 eq234762
    | (have j0 := eq234762 X0
       grind)
    | exact resolve eq234762 eq97315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97315 eq234762
  have eq234827 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq234817 X0
       have j1 := eq97151 X0
       grind)
    | (have r₁ := eq234817 X0
       have r₂ := eq97151 X0
       grind)
    | exact resolve eq234817 eq97151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97151 eq234817
  have eq234947 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ y)) ∨ (σ x) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X1 X0
       have i₂ := eq234827 X1
       grind)
    | exact superpose eq234827 eq368
    | (have j1 := eq234827 X1
       grind)
    | exact resolve eq368 eq234827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234827
  have eq235250 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ (σ x) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq234947 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq234947
    | (have j0 := eq234947 X0 X1
       grind)
    | exact resolve eq234947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234947
  have eq235724 : ∀ X0 X2 : G, (M.op X0 X0) = (τ (σ x)) ∨ (M.op X2 X2) = y := by
    intro X0 X2
    first
    | (have i₁ := eq368 x X0
       have i₂ := eq235250 X2 x
       grind)
    | exact superpose eq235250 eq368
    | (have j1 := eq235250 X2 x
       grind)
    | exact resolve eq368 eq235250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq235250
  have eq236059 : ∀ X0 X2 : G, (M.op X0 X0) = x ∨ (M.op X2 X2) = y := by
    intro X0 X2
    first
    | (have i₁ := eq235724 X0 X2
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq235724
    | (have j0 := eq235724 X0 X2
       grind)
    | exact resolve eq235724 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235724
  have eq236858 : ∀ X1 : G, x = (M.op y x) ∨ x = (M.op X1 X1) := by
    intro X1
    first
    | (have i₁ := eq150631 x
       have i₂ := eq236059 X1 x
       grind)
    | exact superpose eq236059 eq150631
    | (have j1 := eq236059 X1 x
       grind)
    | exact resolve eq150631 eq236059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150631 eq236059
  have eq237257 : ∀ X0 : G, (k x (M.op x y)) = (M.op (M.op x y) x) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq12801 y x
       have i₂ := eq236858 x
       grind)
    | exact superpose eq236858 eq12801
    | (have j1 := eq236858 X0
       grind)
    | exact resolve eq12801 eq236858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12801 eq236858
  have eq237621 : (k x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have j1 := eq162 x x (M.op x y)
       grind)
    | (have r₁ := eq237257 x
       have r₂ := eq162 x x x
       grind)
    | exact resolve eq237257 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237257
  have eq248209 : ∀ X0 : G, (M.op y x) = (k x y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq237621
       have i₂ := eq98131 X0
       grind)
    | exact superpose eq98131 eq237621
    | (have j1 := eq98131 X0
       grind)
    | exact resolve eq237621 eq98131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98131 eq237621
  have eq248210 : (M.op y x) = (k x y) := by
    first
    | (have j1 := eq162 x x y
       grind)
    | (have r₁ := eq248209 x
       have r₂ := eq162 x x x
       grind)
    | exact resolve eq248209 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq248209
  have eq804354 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op y x)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq159244 y X0
       have i₂ := eq248210
       grind)
    | exact superpose eq248210 eq159244
    | exact resolve eq159244 eq248210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159244 eq248210
  have eq804419 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq804354 x
       have i₂ := eq45851 x y x
       grind)
    | exact superpose eq45851 eq804354
    | exact resolve eq804354 eq45851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45851 eq804354
  have eq804424 : False := by grind
  exact eq804424

/-- `Equation417`: `x = x ◇ (x ◇ (y ◇ (x ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation417 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law417 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law417.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq36
    | exact resolve eq36 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq36
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq118 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq121 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq118 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq118 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq118 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq118 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq174 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq121 (σ X0) (σ X1)
       grind)
    | exact superpose eq121 eq15
    | (have j1 := eq121 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq121 (τ X0) X1
       grind)
    | exact superpose eq121 eq18
    | (have j1 := eq121 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq121
  have eq546 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq176
    | exact resolve eq176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq583 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq546
    | (have j0 := eq546 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq546 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq1474 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq174 x y
       grind)
    | exact superpose eq174 eq16
    | (have j1 := eq174 x y
       grind)
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq1600 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1474
       have i₂ := eq583 x y
       grind)
    | exact superpose eq583 eq1474
    | (have j1 := eq583 (σ x) (σ y)
       grind)
    | (have r₁ := eq1474
       have r₂ := eq583 x y
       grind)
    | (have r₁ := eq1474
       have r₂ := eq583 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1474
       have r₂ := eq583 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1474 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq1474
  have eq1601 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1600
  have eq1660 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1601
       grind)
    | exact superpose eq1601 eq10
    | exact resolve eq10 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1704 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1660
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1660
    | exact resolve eq1660 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1660
  have eq1705 : x = y := by grind
  clear eq1704
  have eq1853 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1705
       grind)
    | exact superpose eq1705 eq16
    | exact resolve eq16 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705
  have eq1854 : False := by grind
  exact eq1854
