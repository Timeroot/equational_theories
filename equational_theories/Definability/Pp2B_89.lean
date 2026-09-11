import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation842 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq94 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq152 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 (k (σ X0) (σ X1)) (M.op (σ X0) (σ X1))
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq157 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq152 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq158 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq157 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq164 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq158 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq158
    | (have j0 := eq158 X0 X1
       grind)
    | exact resolve eq158 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq165 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq164 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq368 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq165 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq165
    | exact resolve eq165 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq165 x y
       grind)
    | exact superpose eq165 eq16
    | (have j1 := eq165 x y
       grind)
    | exact resolve eq16 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq386 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq368
  have eq428 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq386 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq386
    | exact resolve eq386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq534 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq374
       have i₂ := eq428 x y
       grind)
    | exact superpose eq428 eq374
    | (have j1 := eq428 (σ x) (σ y)
       grind)
    | (have r₁ := eq374
       have r₂ := eq428 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq374
       have r₂ := eq428 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq374 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374 eq428
  have eq537 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq534
  have eq561 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq537
       grind)
    | exact superpose eq537 eq10
    | exact resolve eq10 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq595 : x = y ∨ x = y := by
    first
    | (have i₁ := eq561
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq561
    | exact resolve eq561 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq596 : x = y := by grind
  clear eq595
  have eq598 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq596
       grind)
    | exact superpose eq596 eq16
    | exact resolve eq16 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq599 : False := by grind
  exact eq599

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation842 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  clear eq18
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq204 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq205 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq1220 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq205 x y
       grind)
    | exact superpose eq205 eq16
    | (have j1 := eq205 x y
       grind)
    | exact resolve eq16 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1222 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq205 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq1740 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq204 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq204
    | exact resolve eq204 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq1897 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1740 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1740
    | (have j0 := eq1740 X0 X1
       grind)
    | exact resolve eq1740 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq2006 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1222 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq1222
    | (have j0 := eq1222 (τ X1) (τ X0)
       grind)
    | exact resolve eq1222 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq2014 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2006 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2006
    | (have j0 := eq2006 X0 X1
       grind)
    | exact resolve eq2006 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq2017 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2014 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2014
    | (have j0 := eq2014 X0 X1
       grind)
    | exact resolve eq2014 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014
  have eq2019 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2017 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2017
    | (have j0 := eq2017 X0 X1
       grind)
    | exact resolve eq2017 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017
  have eq2020 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2019 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2019
    | (have j0 := eq2019 X0 X1
       grind)
    | exact resolve eq2019 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq2021 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2020 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2020
    | (have j0 := eq2020 X0 X1
       grind)
    | exact resolve eq2020 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq2022 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2021 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2021
    | (have j0 := eq2021 X0 X1
       grind)
    | exact resolve eq2021 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021
  have eq6999 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1220
       have i₂ := eq1897 x y
       grind)
    | exact superpose eq1897 eq1220
    | (have j1 := eq1897 (σ x) (σ y)
       grind)
    | (have r₁ := eq1220
       have r₂ := eq1897 x y
       grind)
    | (have r₁ := eq1220
       have r₂ := eq1897 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1220
       have r₂ := eq1897 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1220 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq1897
  have eq7000 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq6999
  have eq7002 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq7000
       grind)
    | exact superpose eq7000 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq7000
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq7000
       grind)
    | exact resolve eq13 eq7000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7000
  have eq7003 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7002
  have eq7004 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7003
  have eq7989 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7004
       grind)
    | exact superpose eq7004 eq16
    | exact resolve eq16 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7004
  have eq7990 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have r₁ := eq7989
       have r₂ := eq22 x
       grind)
    | exact resolve eq7989 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7989
  have eq7993 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq7990
       grind)
    | exact superpose eq7990 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq7990
       grind)
    | exact resolve eq13 eq7990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7990
  have eq7994 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq7993
  have eq7995 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq7994
  have eq7997 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq7995
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq7995
    | exact resolve eq7995 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7995
  have eq8005 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1222 x y
       have i₂ := eq7997
       grind)
    | exact superpose eq7997 eq1222
    | (have j0 := eq1222 x y
       grind)
    | (have r₁ := eq1222 x y
       have r₂ := eq7997
       grind)
    | exact resolve eq1222 eq7997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7997
  have eq8024 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq8005
  have eq8025 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq8024
  have eq8029 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq1222 x y
       grind)
    | (have r₁ := eq8025
       have r₂ := eq1222 x y
       grind)
    | exact resolve eq8025 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222 eq8025
  have eq8032 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8029
       grind)
    | exact superpose eq8029 eq16
    | exact resolve eq16 eq8029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8033 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq8029
       grind)
    | exact superpose eq8029 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8029
       grind)
    | exact resolve eq13 eq8029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8029
  have eq8034 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq8033
  have eq8035 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq8034
  have eq8037 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq8035
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8035
    | exact resolve eq8035 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8035
  have eq8043 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8037
       grind)
    | exact superpose eq8037 eq10
    | exact resolve eq10 eq8037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8037
  have eq8115 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq8043
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8043
    | exact resolve eq8043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8043
  have eq8117 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8115
       grind)
    | exact superpose eq8115 eq16
    | exact resolve eq16 eq8115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8115
  have eq8118 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq8117
       have r₂ := eq22 x
       grind)
    | exact resolve eq8117 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8117
  have eq8128 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq8118
       grind)
    | exact superpose eq8118 eq10
    | exact resolve eq10 eq8118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8118
  have eq8201 : y = (k y x) := by
    first
    | (have i₁ := eq8128
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8128
    | exact resolve eq8128 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8128
  have eq8213 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2022 y x
       have i₂ := eq8201
       grind)
    | exact superpose eq8201 eq2022
    | (have j0 := eq2022 y x
       grind)
    | (have r₁ := eq2022 y x
       have r₂ := eq8201
       grind)
    | exact resolve eq2022 eq8201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022 eq8201
  have eq8225 : y = (M.op x y) ∨ x = y := by grind
  clear eq8213
  have eq8229 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8032
       have i₂ := eq8225
       grind)
    | exact superpose eq8225 eq8032
    | exact resolve eq8032 eq8225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8032 eq8225
  have eq8235 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq8229
  have eq8236 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8235
       grind)
    | exact superpose eq8235 eq16
    | exact resolve eq16 eq8235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8235
  have eq8241 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq8236
       have r₂ := eq22 x
       grind)
    | exact resolve eq8236 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8236
  have eq8242 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8241
       grind)
    | exact superpose eq8241 eq16
    | exact resolve eq16 eq8241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8243 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8241
       grind)
    | exact superpose eq8241 eq10
    | exact resolve eq10 eq8241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8241
  have eq8315 : x = y := by
    first
    | (have i₁ := eq8243
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8243
    | exact resolve eq8243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8243
  have eq8316 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8242
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq8242
    | exact resolve eq8242 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8242
  have eq8317 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8316
       have i₂ := eq8315
       grind)
    | exact superpose eq8315 eq8316
    | exact resolve eq8316 eq8315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8315 eq8316
  have eq8318 : False := by grind
  exact eq8318

/-- `Equation882`: `x = y ◇ ((x ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation882 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law882 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law882.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq55 (τ X0)
       grind)
    | exact superpose eq55 eq18
    | exact resolve eq18 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq63
    | exact resolve eq63 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq63
  have eq80 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq13
    | exact resolve eq13 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq93
    | (have j0 := eq93 X0 X1
       grind)
    | exact resolve eq93 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq93
  have eq322 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96
    | (have j0 := eq96 X1 X1
       grind)
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq349 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq322 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq322
    | (have j0 := eq322 X0 X1
       grind)
    | exact resolve eq322 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq355 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq349 X0 X1
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq349 X0 X0
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq349 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq451 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq355 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq355
    | exact resolve eq355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq355 (σ X1) X0
       grind)
    | exact superpose eq355 eq15
    | (have j1 := eq355 (σ X1) X0
       grind)
    | exact resolve eq15 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq475 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq451
    | (have j0 := eq451 X0 X1
       grind)
    | exact resolve eq451 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq451
  have eq495 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq475 X0 (τ X1)
       grind)
    | exact superpose eq475 eq17
    | (have j1 := eq475 X0 (τ X1)
       grind)
    | exact resolve eq17 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq475
  have eq1092 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq495 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq495
    | exact resolve eq495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq1142 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1092 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1092
    | (have j0 := eq1092 X0 X1
       grind)
    | exact resolve eq1092 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq4572 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq462 x y
       grind)
    | exact superpose eq462 eq16
    | (have j1 := eq462 x y
       grind)
    | exact resolve eq16 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4619 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq462 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq4722 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4572
       have i₂ := eq1142 y x
       grind)
    | exact superpose eq1142 eq4572
    | (have j1 := eq1142 y x
       grind)
    | (have r₁ := eq4572
       have r₂ := eq1142 y x
       grind)
    | exact resolve eq4572 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4572
  have eq4723 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4722
  have eq4728 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq4723
       grind)
    | exact superpose eq4723 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4723
       grind)
    | exact resolve eq13 eq4723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4723
  have eq4745 : (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4728
  have eq28170 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4619 x y
       have i₂ := eq4745
       grind)
    | exact superpose eq4745 eq4619
    | (have j0 := eq4619 x y
       grind)
    | exact resolve eq4619 eq4745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4619 eq4745
  have eq28181 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq28170
  have eq28182 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq28181
  have eq28327 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28182
       grind)
    | exact superpose eq28182 eq16
    | exact resolve eq16 eq28182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28328 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq80 x (σ y)
       have i₂ := eq28182
       grind)
    | exact superpose eq28182 eq80
    | (have j0 := eq80 x (σ y)
       grind)
    | (have r₁ := eq80 x (σ y)
       have r₂ := eq28182
       grind)
    | exact resolve eq80 eq28182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq28182
  have eq28400 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq28328
  have eq28434 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28400
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq28400
    | exact resolve eq28400 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28400
  have eq29003 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1142 y x
       have i₂ := eq28434
       grind)
    | exact superpose eq28434 eq1142
    | (have j0 := eq1142 y x
       grind)
    | exact resolve eq1142 eq28434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142 eq28434
  have eq29105 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq29003
       have r₂ := eq28327
       grind)
    | exact resolve eq29003 eq28327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29003
  have eq29316 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28327
       have i₂ := eq29105
       grind)
    | exact superpose eq29105 eq28327
    | exact resolve eq28327 eq29105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28327 eq29105
  have eq29381 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq29316
  have eq29382 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq29381
  have eq29387 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq29382
       grind)
    | exact superpose eq29382 eq10
    | exact resolve eq10 eq29382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29382
  have eq29483 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29387
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29387
    | exact resolve eq29387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29387
  have eq29484 : x = (M.op x x) := by grind
  clear eq29483
  have eq29596 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq29484
       grind)
    | exact superpose eq29484 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq29484
       grind)
    | exact resolve eq12 eq29484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29597 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq81 x X0
       have i₂ := eq29484
       grind)
    | exact superpose eq29484 eq81
    | (have j0 := eq81 x X0
       grind)
    | exact resolve eq81 eq29484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq29484
  have eq29644 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq29597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29597
  have eq29645 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq29596 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29596
  have eq31147 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq29644 (σ X0)
       grind)
    | exact superpose eq29644 eq15
    | exact resolve eq15 eq29644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29644
  have eq31252 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq31147 X0
       have i₂ := eq29645 X0
       grind)
    | exact superpose eq29645 eq31147
    | exact resolve eq31147 eq29645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29645 eq31147
  have eq33470 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31252 y
       grind)
    | exact superpose eq31252 eq16
    | (have r₁ := eq16
       have r₂ := eq31252 y
       grind)
    | exact resolve eq16 eq31252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31252
  have eq33628 : False := by grind
  exact eq33628

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pxx_x_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq17 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq19 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq20 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq22 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : (M.op x y) = (M.op x y) := by grind
  have eq24 : (M.op x y) = (M.op x y) := by grind
  clear eq23
  have eq25 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq25
  have eq27 : (σ x) = (σ x) := by grind
  have eq28 : (σ x) = (σ x) := by grind
  clear eq27
  have eq29 : (σ y) = (σ y) := by grind
  have eq30 : (σ y) = (σ y) := by grind
  clear eq29
  have eq31 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq31
  have eq33 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq34 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq19 eq18
    | (have j1 := eq19 X0
       grind)
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19
  have eq35 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq22 eq21
    | (have j1 := eq22 X0
       grind)
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq36 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq34
    | (have j0 := eq34 (M.op x y)
       grind)
    | exact resolve eq34 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq34 x
       have i₂ := eq28
       grind)
    | exact superpose eq28 eq34
    | (have j0 := eq34 x
       grind)
    | exact resolve eq34 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq34 y
       have i₂ := eq30
       grind)
    | exact superpose eq30 eq34
    | (have j0 := eq34 y
       grind)
    | exact resolve eq34 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq41 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38
       grind)
    | exact superpose eq38 eq24
    | exact resolve eq24 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38
  have eq42 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq41
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq41
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq41
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34
    | exact resolve eq34 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (τ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (τ (k (k (σ X0) (σ X1)) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 (k X0 X1) X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq46
    | exact resolve eq46 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq26 eq46
    | (have j0 := eq46 (M.op x y) X0
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq26 eq46
    | (have j0 := eq46 X0 (M.op x y)
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
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
  have eq63 : (τ (σ y)) = (M.op (τ (σ x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq32 eq9
    | (have j0 := eq9 (σ y) (σ x)
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (M.op (τ (σ y)) (τ (σ y)))) := by
    first
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | (have i₁ := eq106
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq106
    | exact resolve eq106 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq109 : (k (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | (have i₁ := eq107
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq107
    | exact resolve eq107 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq130 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq14
    | (have j0 := eq14 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq133
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq133
    | exact resolve eq133 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq156 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq130
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq130
    | exact resolve eq130 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq167 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq153
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq153
    | exact resolve eq153 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq170 : (k (τ (σ y)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq156
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq156
    | exact resolve eq156 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq203 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq47
    | exact resolve eq47 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : (k (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq109 eq9
    | exact resolve eq9 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : (k (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq289
       have i₂ := eq83 (k sF2 sF2)
       grind)
    | exact superpose eq83 eq289
    | exact resolve eq289 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq298 : ∀ X0 : G, (M.op X0 (M.op (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq12
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (M.op X0 (k (M.op X0 X1) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq83 (M.op X0 X1)
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : (σ y) = (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq65
       have i₂ := eq83 sF6
       grind)
    | exact superpose eq83 eq65
    | exact resolve eq65 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq304 : ∀ X0 : G, (M.op X0 (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq298 X0
       have i₂ := eq83 (k X0 X0)
       grind)
    | exact superpose eq83 eq298
    | exact resolve eq298 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq440 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (M.op X0 X1)
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq83
    | exact resolve eq83 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op X0 (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq441
    | exact resolve eq441 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq448 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq440 X0 X1
       have i₂ := eq83 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq83 eq440
    | exact resolve eq440 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq465 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 X1
       have i₂ := eq447 (M.op X0 X1) (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq447 eq448
    | exact resolve eq448 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq480 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 (k X1 X1))) (M.op (M.op X0 X1) (M.op X0 (k X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq465 X0 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq465
    | exact resolve eq465 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq493 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (k (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) (k (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq480 X0 X1
       have i₂ := eq447 X0 X1
       grind)
    | exact superpose eq447 eq480
    | exact resolve eq480 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq498 : ∀ X0 X1 : G, (M.op X0 X1) = (k (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X1
       have i₂ := eq447 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq447 eq493
    | exact resolve eq493 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq500 : ∀ X0 X1 : G, (M.op X0 X1) = (k (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq498 X0 X1
       have i₂ := eq83 (M.op X0 X1)
       grind)
    | exact superpose eq83 eq498
    | exact resolve eq498 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq602 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq290 eq62
    | exact resolve eq62 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq609 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq602
       have i₂ := eq83 (k (k sF2 sF2) (k sF2 sF2))
       grind)
    | exact superpose eq83 eq602
    | exact resolve eq602 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq614 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (k (M.op (τ (σ x)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) (M.op (τ (σ x)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq609
       have i₂ := eq447 (τ sF4) (k (k sF2 sF2) (k sF2 sF2))
       grind)
    | exact superpose eq447 eq609
    | exact resolve eq609 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq617 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (k (k (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) (M.op (τ (σ x)) (k (M.op x y) (M.op x y)))) (k (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) (M.op (τ (σ x)) (k (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq614
       have i₂ := eq447 (τ sF4) (k sF2 sF2)
       grind)
    | exact superpose eq447 eq614
    | exact resolve eq614 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq619 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (k (k (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))) (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y)))) (k (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))) (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))))) := by
    first
    | (have i₁ := eq617
       have i₂ := eq447 (τ sF4) sF2
       grind)
    | exact superpose eq447 eq617
    | exact resolve eq617 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq621 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (M.op x y)) := by
    first
    | (have i₁ := eq619
       have i₂ := eq500 (τ sF4) sF2
       grind)
    | exact superpose eq500 eq619
    | exact resolve eq619 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq619
  have eq623 : (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (M.op x y)) := by
    first
    | (have i₁ := eq621
       have i₂ := eq83 (k (τ sF5) (τ sF5))
       grind)
    | exact superpose eq83 eq621
    | exact resolve eq621 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq625 : (M.op (τ (σ x)) (M.op (M.op x y) (M.op x y))) = (M.op (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    first
    | exact superpose eq623 eq62
    | exact resolve eq62 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq632 : (M.op (τ (σ x)) (M.op (M.op x y) (M.op x y))) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    first
    | (have i₁ := eq625
       have i₂ := eq83 (k (k (τ sF5) (τ sF5)) (k (τ sF5) (τ sF5)))
       grind)
    | exact superpose eq83 eq625
    | exact resolve eq625 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq637 : (τ (σ y)) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    first
    | exact superpose eq63 eq632
    | exact resolve eq632 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq632
  have eq651 : (τ (σ x)) = (M.op (τ (σ y)) (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq170 eq9
    | exact resolve eq9 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq652 : (τ (σ x)) = (M.op (τ (σ y)) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq651
       have i₂ := eq83 (k (τ sF5) (τ sF5))
       grind)
    | exact superpose eq83 eq651
    | exact resolve eq651 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq657 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq652
       have i₂ := eq304 (τ sF5)
       grind)
    | exact superpose eq304 eq652
    | exact resolve eq652 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq675 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq657 eq15
    | exact resolve eq15 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq679 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq675
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq675
    | exact resolve eq675 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq683 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq679
    | exact resolve eq679 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq685 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq683 eq15
    | exact resolve eq15 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq686 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq685
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq685
    | exact resolve eq685 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq687 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq686
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq686
    | exact resolve eq686 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq688 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq687
    | exact resolve eq687 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq712 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq688 eq36
    | exact resolve eq36 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq728 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq712
       have i₂ := eq203 sF5 sF5
       grind)
    | exact superpose eq203 eq712
    | exact resolve eq712 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq1420 : ∀ X0 : G, (k (M.op X0 (τ (σ y))) (M.op X0 (τ (σ y)))) = (M.op X0 (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq728 eq447
    | exact resolve eq447 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq1439 : ∀ X0 : G, (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq304 X0
       have i₂ := eq447 X0 (k X0 X0)
       grind)
    | exact superpose eq447 eq304
    | exact resolve eq304 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1440 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq301 X0 X1
       have i₂ := eq447 X0 (M.op X0 X1)
       grind)
    | exact superpose eq447 eq301
    | exact resolve eq301 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1443 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) ≠ (k (M.op (k X0 X0) X0) (M.op (k X0 X0) X0)) ∨ (k (k X0 X0) X1) = (k (M.op (k X0 X0) X0) (M.op (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (k X1 X1) X1
       have i₂ := eq447 (k X1 X1) X1
       grind)
    | exact superpose eq447 eq12
    | exact resolve eq12 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1457 : (σ y) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq303
       have i₂ := eq447 sF4 sF6
       grind)
    | exact superpose eq447 eq303
    | exact resolve eq303 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1471 : ∀ X0 : G, (k (k (M.op X0 X0) (M.op X0 X0)) (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1439 x
       have i₂ := eq447 x x
       grind)
    | exact superpose eq447 eq1439
    | exact resolve eq1439 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1487 : ∀ X0 : G, (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1471 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq1471
    | exact resolve eq1471 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471
  have eq1744 : (M.op x y) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq299
    | (have j0 := eq299 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq299 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1753 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq299
    | (have j0 := eq299 (σ y) (σ x)
       grind)
    | exact resolve eq299 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq2001 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (M.op X0 (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq1420 eq301
    | exact resolve eq301 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq1420
  have eq2031 : (τ (σ y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2001 sF2
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq2001
    | exact resolve eq2001 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001
  have eq2057 : (τ (σ y)) = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2031
       have i₂ := eq447 sF2 sF2
       grind)
    | exact superpose eq447 eq2031
    | exact resolve eq2031 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031
  have eq2067 : (τ (σ y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2057
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq2057
    | exact resolve eq2057 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq2094 : (σ y) = (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2067 eq35
    | exact resolve eq35 eq2067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067
  have eq2109 : (σ y) = (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2094
       have i₂ := eq15 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq15 eq2094
    | exact resolve eq2094 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094
  have eq2124 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2109
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq2109
    | exact resolve eq2109 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109
  have eq2132 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq2124
    | exact resolve eq2124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq2192 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2132 eq304
    | exact resolve eq304 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132
  have eq2227 : (M.op x y) = (τ (k (σ y) (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2192 eq36
    | exact resolve eq36 eq2192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2228 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (k (σ y) (σ x)) (σ X0))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq2192 eq51
    | exact resolve eq51 eq2192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2229 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (k (σ y) (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq2192 eq56
    | exact resolve eq56 eq2192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2242 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (k (σ y) (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2229 x
       have i₂ := eq52 (k sF5 sF4) x
       grind)
    | exact superpose eq52 eq2229
    | exact resolve eq2229 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq2229
  have eq2243 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (k (σ y) (σ x))) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2228 x
       have i₂ := eq47 (k sF5 sF4) x
       grind)
    | exact superpose eq47 eq2228
    | exact resolve eq2228 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq2228
  have eq2244 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2227
       have i₂ := eq203 sF4 sF5
       grind)
    | exact superpose eq203 eq2227
    | exact resolve eq2227 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227
  have eq2251 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (k (τ (σ y)) (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2242 X0
       have i₂ := eq203 sF4 sF5
       grind)
    | exact superpose eq203 eq2242
    | exact resolve eq2242 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242
  have eq2252 : ∀ X0 : G, (k (M.op x y) X0) = (k (k (τ (σ y)) (τ (σ x))) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2243 X0
       have i₂ := eq203 sF4 sF5
       grind)
    | exact superpose eq203 eq2243
    | exact resolve eq2243 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2243
  have eq8066 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X1 (M.op X1 X0))) (τ (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq203 (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))
       have i₂ := eq1440 X1 X0
       grind)
    | exact superpose eq1440 eq203
    | exact resolve eq203 eq1440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8186 : (τ (σ x)) = (k (τ (M.op (σ y) (k (σ y) (σ y)))) (τ (M.op (σ y) (k (σ y) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq167 eq8066
    | exact resolve eq8066 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq8066
  have eq8233 : (τ (σ x)) = (k (τ (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) (τ (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8186
       have i₂ := eq447 sF5 sF5
       grind)
    | exact superpose eq447 eq8186
    | exact resolve eq8186 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8186
  have eq8282 : (τ (σ x)) = (k (k (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) (k (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8233
       have i₂ := eq203 (M.op sF5 sF5) (M.op sF5 sF5)
       grind)
    | exact superpose eq203 eq8233
    | exact resolve eq8233 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8233
  have eq8325 : (τ (σ x)) = (k (k (τ (k (σ y) (σ y))) (τ (k (σ y) (σ y)))) (k (τ (k (σ y) (σ y))) (τ (k (σ y) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8282
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq8282
    | exact resolve eq8282 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8282
  have eq8361 : (τ (σ x)) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8325
       have i₂ := eq203 sF5 sF5
       grind)
    | exact superpose eq203 eq8325
    | exact resolve eq8325 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8325
  have eq8389 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq637 eq8361
    | exact resolve eq8361 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8361
  have eq8458 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq8389 eq33
    | exact resolve eq33 eq8389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8468 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  have eq8972 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq8389 eq1753
    | (have r₁ := eq1753
       have r₂ := eq8389
       grind)
    | exact resolve eq1753 eq8389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753 eq8389
  have eq8976 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq8972
  have eq11629 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq8976 eq300
    | (have j0 := eq300 (σ y) (σ x)
       grind)
    | (have r₁ := eq300 (σ y) (σ x)
       have r₂ := eq8976
       grind)
    | exact resolve eq300 eq8976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq8976
  have eq11645 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq11629
  have eq11658 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq11645
       have r₂ := eq8468
       grind)
    | exact resolve eq11645 eq8468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11645
  have eq11771 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq11658 eq33
    | exact resolve eq33 eq11658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11658
  have eq11812 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2192 eq11771
    | (have r₁ := eq11771
       have r₂ := eq2192
       grind)
    | exact resolve eq11771 eq2192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11815 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq11812
  have eq11816 : (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq11815
  have eq12148 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11816 eq203
    | exact resolve eq203 eq11816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12470 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq12148 eq2251
    | exact resolve eq2251 eq12148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251
  have eq12471 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (σ y)) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq12148 eq2252
    | exact resolve eq2252 eq12148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2252
  have eq12483 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (σ y)) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq12471 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12471
  have eq12484 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq12470 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12470
  have eq13052 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12483 eq2244
    | exact resolve eq2244 eq12483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq13060 : (τ (σ y)) = (k (M.op x y) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12483 eq12148
    | exact resolve eq12148 eq12483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12148 eq12483
  have eq13120 : (τ (σ y)) = (k (M.op x y) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq13060
  have eq13125 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq13052
  have eq13408 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13125 eq15
    | exact resolve eq15 eq13125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13125
  have eq13426 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq13408
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq13408
    | exact resolve eq13408 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13408
  have eq13432 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq13426
    | exact resolve eq13426 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13426
  have eq13446 : (σ (σ (M.op x y))) = (k (σ (σ (M.op x y))) (σ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13432 eq15
    | exact resolve eq15 eq13432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13432
  have eq13616 : (σ y) = (σ (k (M.op x y) (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13120 eq35
    | exact resolve eq35 eq13120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13120
  have eq13629 : (σ y) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq13616
       have i₂ := eq15 sF2 (τ sF4)
       grind)
    | exact superpose eq15 eq13616
    | exact resolve eq13616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13616
  have eq13650 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq13629
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq13629
    | exact resolve eq13629 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13629
  have eq13656 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq13650
    | exact resolve eq13650 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13650
  have eq13674 : (σ (σ y)) = (k (σ (σ (M.op x y))) (σ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13656 eq15
    | exact resolve eq15 eq13656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13656
  have eq15456 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (τ (σ y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq12484 eq15
    | exact resolve eq15 eq12484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12484
  have eq15532 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15456 X0
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq15456
    | exact resolve eq15456 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15456
  have eq15534 : ∀ X0 : G, (k (σ X0) (σ y)) = (k (σ X0) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15532 X0
       have i₂ := eq15 X0 sF2
       grind)
    | exact superpose eq15 eq15532
    | exact resolve eq15532 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15532
  have eq15535 : ∀ X0 : G, (k (σ X0) (σ y)) = (k (σ X0) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq15534
    | (have j0 := eq15534 X0
       grind)
    | exact resolve eq15534 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15534
  have eq16718 : ∀ X0 : G, (k (k (σ (M.op x y)) (σ x)) X0) = (τ (k (σ (σ (M.op x y))) (σ X0))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq13446 eq48
    | exact resolve eq48 eq13446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13446
  have eq16747 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (k (σ (M.op x y)) (σ x)) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16718 x
       have i₂ := eq46 sF3 x
       grind)
    | exact superpose eq46 eq16718
    | exact resolve eq16718 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16718
  have eq16835 : ∀ X0 : G, (τ (k (σ (σ y)) (σ X0))) = (k (k (σ (M.op x y)) (σ x)) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq13674 eq48
    | exact resolve eq48 eq13674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq13674
  have eq16866 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ (M.op x y)) (σ x)) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16835 x
       have i₂ := eq46 sF5 x
       grind)
    | exact superpose eq46 eq16835
    | exact resolve eq16835 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq16835
  have eq19983 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15535 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15535
    | exact resolve eq15535 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15535
  have eq24277 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (k (σ (M.op x y)) (σ x)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16747 eq19983
    | exact resolve eq19983 eq16747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16747 eq19983
  have eq24278 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (k (σ (M.op x y)) (σ x)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq24277
  have eq29355 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq24278 eq16866
    | exact resolve eq16866 eq24278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16866 eq24278
  have eq29371 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq29355
  have eq29475 : (k (M.op x y) (M.op x y)) = (τ (k (σ y) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq29371 eq72
    | exact resolve eq72 eq29371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq29657 : (k (M.op x y) (M.op x y)) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq29475
       have i₂ := eq203 sF5 sF5
       grind)
    | exact superpose eq203 eq29475
    | exact resolve eq29475 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29475
  have eq31934 : (k (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq29657 eq109
    | exact resolve eq109 eq29657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq29657
  have eq32049 : (k (M.op x y) (M.op x y)) = (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq31934
       have i₂ := eq447 (τ sF4) sF2
       grind)
    | exact superpose eq447 eq31934
    | exact resolve eq31934 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31934
  have eq32066 : (k (M.op x y) (M.op x y)) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq623 eq32049
    | exact resolve eq32049 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq32049
  have eq32071 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq637 eq32066
    | exact resolve eq32066 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq32066
  have eq32229 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq32071 eq35
    | exact resolve eq35 eq32071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32071
  have eq32247 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq32229
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq32229
    | exact resolve eq32229 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32229
  have eq32283 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq32247
    | exact resolve eq32247 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32247
  have eq32361 : (σ y) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq32283 eq29371
    | exact resolve eq29371 eq32283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29371 eq32283
  have eq32436 : (σ y) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq32361
  have eq33067 : (σ y) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq32436 eq8468
    | exact resolve eq8468 eq32436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8468 eq32436
  have eq33132 : (σ y) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq33067
  have eq33162 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq33132
       have r₂ := eq11816
       grind)
    | exact resolve eq33132 eq11816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11816 eq33132
  have eq33175 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq33162 eq33
    | exact resolve eq33 eq33162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33162
  have eq33228 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have r₁ := eq33175
       have r₂ := eq2192
       grind)
    | exact resolve eq33175 eq2192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2192 eq33175
  have eq33416 : (σ y) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33228 eq1440
    | exact resolve eq1440 eq33228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33228
  have eq33446 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq33416
       have i₂ := eq83 sF3
       grind)
    | exact superpose eq83 eq33416
    | exact resolve eq33416 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33416
  have eq33873 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33446 eq1487
    | exact resolve eq1487 eq33446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487 eq33446
  have eq34017 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33873 eq36
    | exact resolve eq36 eq33873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq34065 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33873 eq8458
    | (have r₁ := eq8458
       have r₂ := eq33873
       grind)
    | exact resolve eq8458 eq33873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8458
  have eq34207 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq34065
  have eq34208 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq34207
  have eq34264 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq34017
       have i₂ := eq203 sF5 sF5
       grind)
    | exact superpose eq203 eq34017
    | exact resolve eq34017 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq34017
  have eq34340 : (σ y) = (k (M.op (σ x) (k (σ y) (σ x))) (M.op (σ x) (k (σ y) (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq34208 eq1457
    | exact resolve eq1457 eq34208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457 eq34208
  have eq34484 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq34264 eq1744
    | (have r₁ := eq1744
       have r₂ := eq34264
       grind)
    | exact resolve eq1744 eq34264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744
  have eq34493 : (τ (σ y)) = (M.op (τ (σ y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq34264 eq304
    | exact resolve eq304 eq34264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq34264
  have eq34542 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq34484
  have eq34561 : (τ (σ y)) = (k (M.op (τ (σ y)) (M.op x y)) (M.op (τ (σ y)) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq34493
       have i₂ := eq447 (τ sF5) sF2
       grind)
    | exact superpose eq447 eq34493
    | exact resolve eq34493 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq34493
  have eq47959 : ∀ X0 : G, (M.op (τ (σ y)) X0) ≠ (k (M.op (τ (σ y)) (M.op (τ (σ y)) (M.op x y))) (M.op (τ (σ y)) (M.op (τ (σ y)) (M.op x y)))) ∨ (k (τ (σ y)) X0) = (k (M.op (τ (σ y)) (M.op (τ (σ y)) (M.op x y))) (M.op (τ (σ y)) (M.op (τ (σ y)) (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq34561 eq1443
    | exact resolve eq1443 eq34561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443 eq34561
  have eq48030 : ∀ X0 : G, (M.op x y) ≠ (M.op (τ (σ y)) X0) ∨ (k (τ (σ y)) X0) = (k (M.op (τ (σ y)) (M.op (τ (σ y)) (M.op x y))) (M.op (τ (σ y)) (M.op (τ (σ y)) (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq47959 X0
       have i₂ := eq1440 (τ sF5) sF2
       grind)
    | exact superpose eq1440 eq47959
    | (have j0 := eq47959 X0
       grind)
    | exact resolve eq47959 eq1440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47959
  have eq48045 : ∀ X0 : G, (M.op x y) ≠ (M.op (τ (σ y)) X0) ∨ (M.op x y) = (k (τ (σ y)) X0) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq48030 X0
       have i₂ := eq1440 (τ sF5) sF2
       grind)
    | exact superpose eq1440 eq48030
    | (have j0 := eq48030 X0
       grind)
    | exact resolve eq48030 eq1440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440 eq48030
  have eq177765 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq34542 eq15
    | exact resolve eq15 eq34542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34542
  have eq177820 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq177765
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq177765
    | exact resolve eq177765 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177765
  have eq177833 : (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq177820
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq177820
    | exact resolve eq177820 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177820
  have eq177851 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq177833 eq48045
    | (have j0 := eq48045 (τ (σ x))
       grind)
    | (have r₁ := eq48045 (τ (σ x))
       have r₂ := eq177833
       grind)
    | exact resolve eq48045 eq177833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48045 eq177833
  have eq177921 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq177851
  have eq177922 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq177921
  have eq178211 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq177922 eq15
    | exact resolve eq15 eq177922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177922
  have eq178261 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq178211
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq178211
    | exact resolve eq178211 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178211
  have eq178269 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq178261
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq178261
    | exact resolve eq178261 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178261
  have eq178270 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq178269
    | exact resolve eq178269 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178269
  have eq178271 : (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have r₁ := eq178270
       have r₂ := eq11771
       grind)
    | exact resolve eq178270 eq11771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11771 eq178270
  have eq178284 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq178271 eq34340
    | exact resolve eq34340 eq178271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34340 eq178271
  have eq178345 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq178284
  have eq178402 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq178345
    | exact resolve eq178345 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178345
  have eq179340 : (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq178402 eq303
    | exact resolve eq303 eq178402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq179567 : (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq179340
    | exact resolve eq179340 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179340
  have eq180345 : (σ y) = (σ (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq179567 eq35
    | exact resolve eq35 eq179567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179567
  have eq180347 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq180345
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq180345
    | exact resolve eq180345 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180345
  have eq180367 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq180347 eq33
    | exact resolve eq33 eq180347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180439 : (σ y) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq180347 eq178402
    | exact resolve eq178402 eq180347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178402 eq180347
  have eq181263 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33873 eq180367
    | exact resolve eq180367 eq33873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33873 eq180367
  have eq181264 : (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq181263
       have r₂ := eq180439
       grind)
    | exact resolve eq181263 eq180439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180439 eq181263
  have eq182025 : (σ y) = (σ (τ (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq181264 eq35
    | exact resolve eq35 eq181264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181264
  have eq182028 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq182025
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq182025
    | exact resolve eq182025 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182025
  have eq182029 : (σ x) = (σ y) := by grind
  clear eq182028
  have eq182032 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq182029 eq32
    | exact resolve eq32 eq182029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq182033 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq182029 eq42
    | exact resolve eq42 eq182029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq182029
  have eq182126 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq182033
       have i₂ := eq83 (τ sF4)
       grind)
    | exact superpose eq83 eq182033
    | exact resolve eq182033 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182033
  have eq182127 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq182032
       have i₂ := eq83 sF4
       grind)
    | exact superpose eq83 eq182032
    | exact resolve eq182032 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq182032
  have eq182690 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq182127 eq33
    | exact resolve eq33 eq182127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq182127
  have eq183322 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) := by
    first
    | exact superpose eq182126 eq15
    | exact resolve eq15 eq182126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182126
  have eq183442 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq183322
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq183322
    | exact resolve eq183322 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq183322
  have eq183557 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq183442 eq26
    | exact resolve eq26 eq183442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq183442
  have eq183613 : False := by grind
  exact eq183613

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pxx_y_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq17 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq19 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq20 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq22 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : (M.op x y) = (M.op x y) := by grind
  have eq24 : (M.op x y) = (M.op x y) := by grind
  clear eq23
  have eq25 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq25
  have eq27 : (σ x) = (σ x) := by grind
  have eq28 : (σ x) = (σ x) := by grind
  clear eq27
  have eq29 : (σ y) = (σ y) := by grind
  have eq30 : (σ y) = (σ y) := by grind
  clear eq29
  have eq31 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq31
  have eq33 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq34 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq19 eq18
    | (have j1 := eq19 X0
       grind)
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19
  have eq35 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq22 eq21
    | (have j1 := eq22 X0
       grind)
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq36 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq34
    | (have j0 := eq34 (M.op x y)
       grind)
    | exact resolve eq34 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq34 x
       have i₂ := eq28
       grind)
    | exact superpose eq28 eq34
    | (have j0 := eq34 x
       grind)
    | exact resolve eq34 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq34 y
       have i₂ := eq30
       grind)
    | exact superpose eq30 eq34
    | (have j0 := eq34 y
       grind)
    | exact resolve eq34 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq41 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38
       grind)
    | exact superpose eq38 eq24
    | exact resolve eq24 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38
  have eq42 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq41
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq41
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq41
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34
    | exact resolve eq34 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (τ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (τ (k (k (σ X0) (σ X1)) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 (k X0 X1) X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq46
    | exact resolve eq46 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq26 eq46
    | (have j0 := eq46 (M.op x y) X0
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq26 eq46
    | (have j0 := eq46 X0 (M.op x y)
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
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
  have eq63 : (τ (σ y)) = (M.op (τ (σ x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq32 eq9
    | (have j0 := eq9 (σ y) (σ x)
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (M.op (τ (σ y)) (τ (σ y)))) := by
    first
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | (have i₁ := eq106
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq106
    | exact resolve eq106 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq109 : (k (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | (have i₁ := eq107
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq107
    | exact resolve eq107 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq130 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq14
    | (have j0 := eq14 (τ (σ x)) (τ (σ y))
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq133
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq133
    | exact resolve eq133 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq156 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq130
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq130
    | exact resolve eq130 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq167 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq153
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq153
    | exact resolve eq153 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq170 : (k (τ (σ y)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq156
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq156
    | exact resolve eq156 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq203 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq47
    | exact resolve eq47 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq289 : (k (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq109 eq9
    | exact resolve eq9 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : (k (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq289
       have i₂ := eq83 (k sF2 sF2)
       grind)
    | exact superpose eq83 eq289
    | exact resolve eq289 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq298 : ∀ X0 : G, (M.op X0 (M.op (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (M.op X0 (k (M.op X0 X1) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq83 (M.op X0 X1)
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : (σ y) = (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq65
       have i₂ := eq83 sF6
       grind)
    | exact superpose eq83 eq65
    | exact resolve eq65 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq305 : ∀ X0 : G, (M.op X0 (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq298 X0
       have i₂ := eq83 (k X0 X0)
       grind)
    | exact superpose eq83 eq298
    | exact resolve eq298 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq441 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (M.op X0 X1)
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq83
    | exact resolve eq83 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op X0 (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq442 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq442
    | exact resolve eq442 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq449 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X1
       have i₂ := eq83 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq83 eq441
    | exact resolve eq441 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq466 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq449 X0 X1
       have i₂ := eq448 (M.op X0 X1) (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq448 eq449
    | exact resolve eq449 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq481 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 (k X1 X1))) (M.op (M.op X0 X1) (M.op X0 (k X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq466
    | exact resolve eq466 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq493 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (k (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) (k (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq481 X0 X1
       have i₂ := eq448 X0 X1
       grind)
    | exact superpose eq448 eq481
    | exact resolve eq481 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq498 : ∀ X0 X1 : G, (M.op X0 X1) = (k (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X1
       have i₂ := eq448 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq448 eq493
    | exact resolve eq493 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq500 : ∀ X0 X1 : G, (M.op X0 X1) = (k (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq498 X0 X1
       have i₂ := eq83 (M.op X0 X1)
       grind)
    | exact superpose eq83 eq498
    | exact resolve eq498 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq602 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq290 eq62
    | exact resolve eq62 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq609 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq602
       have i₂ := eq83 (k (k sF2 sF2) (k sF2 sF2))
       grind)
    | exact superpose eq83 eq602
    | exact resolve eq602 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq614 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (k (M.op (τ (σ x)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) (M.op (τ (σ x)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq609
       have i₂ := eq448 (τ sF4) (k (k sF2 sF2) (k sF2 sF2))
       grind)
    | exact superpose eq448 eq609
    | exact resolve eq609 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq617 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (k (k (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) (M.op (τ (σ x)) (k (M.op x y) (M.op x y)))) (k (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) (M.op (τ (σ x)) (k (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq614
       have i₂ := eq448 (τ sF4) (k sF2 sF2)
       grind)
    | exact superpose eq448 eq614
    | exact resolve eq614 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq619 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (k (k (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))) (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y)))) (k (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))) (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))))) := by
    first
    | (have i₁ := eq617
       have i₂ := eq448 (τ sF4) sF2
       grind)
    | exact superpose eq448 eq617
    | exact resolve eq617 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq621 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (M.op x y)) := by
    first
    | (have i₁ := eq619
       have i₂ := eq500 (τ sF4) sF2
       grind)
    | exact superpose eq500 eq619
    | exact resolve eq619 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq619
  have eq623 : (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (M.op x y)) := by
    first
    | (have i₁ := eq621
       have i₂ := eq83 (k (τ sF5) (τ sF5))
       grind)
    | exact superpose eq83 eq621
    | exact resolve eq621 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq625 : (M.op (τ (σ x)) (M.op (M.op x y) (M.op x y))) = (M.op (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    first
    | exact superpose eq623 eq62
    | exact resolve eq62 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq632 : (M.op (τ (σ x)) (M.op (M.op x y) (M.op x y))) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    first
    | (have i₁ := eq625
       have i₂ := eq83 (k (k (τ sF5) (τ sF5)) (k (τ sF5) (τ sF5)))
       grind)
    | exact superpose eq83 eq625
    | exact resolve eq625 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq637 : (τ (σ y)) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    first
    | exact superpose eq63 eq632
    | exact resolve eq632 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq632
  have eq650 : (τ (σ x)) = (M.op (τ (σ y)) (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq170 eq9
    | exact resolve eq9 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq651 : (τ (σ x)) = (M.op (τ (σ y)) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq650
       have i₂ := eq83 (k (τ sF5) (τ sF5))
       grind)
    | exact superpose eq83 eq650
    | exact resolve eq650 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq656 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq651
       have i₂ := eq305 (τ sF5)
       grind)
    | exact superpose eq305 eq651
    | exact resolve eq651 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq671 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq656 eq15
    | exact resolve eq15 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq675 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq671
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq671
    | exact resolve eq671 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq679 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq675
    | exact resolve eq675 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq704 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq679 eq15
    | exact resolve eq15 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq705 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq704
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq704
    | exact resolve eq704 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq706 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq705
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq705
    | exact resolve eq705 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq707 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq706
    | exact resolve eq706 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq708 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq707 eq36
    | exact resolve eq36 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq724 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq708
       have i₂ := eq203 sF5 sF5
       grind)
    | exact superpose eq203 eq708
    | exact resolve eq708 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq1464 : ∀ X0 : G, (k (M.op X0 (τ (σ y))) (M.op X0 (τ (σ y)))) = (M.op X0 (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq724 eq448
    | exact resolve eq448 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq1484 : ∀ X0 : G, (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq305 X0
       have i₂ := eq448 X0 (k X0 X0)
       grind)
    | exact superpose eq448 eq305
    | exact resolve eq305 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1485 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq301 X0 X1
       have i₂ := eq448 X0 (M.op X0 X1)
       grind)
    | exact superpose eq448 eq301
    | exact resolve eq301 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1502 : (σ y) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq303
       have i₂ := eq448 sF4 sF6
       grind)
    | exact superpose eq448 eq303
    | exact resolve eq303 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1517 : ∀ X0 : G, (k (k (M.op X0 X0) (M.op X0 X0)) (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1484 x
       have i₂ := eq448 x x
       grind)
    | exact superpose eq448 eq1484
    | exact resolve eq1484 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq1534 : ∀ X0 : G, (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1517 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq1517
    | exact resolve eq1517 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq1755 : (M.op x y) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq42 eq299
    | (have j0 := eq299 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq299 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1764 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq299
    | (have j0 := eq299 (σ y) (σ x)
       grind)
    | exact resolve eq299 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq2001 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (M.op X0 (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1464 eq301
    | exact resolve eq301 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq1464
  have eq2057 : (τ (σ y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2001 sF2
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq2001
    | exact resolve eq2001 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001
  have eq2083 : (τ (σ y)) = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2057
       have i₂ := eq448 sF2 sF2
       grind)
    | exact superpose eq448 eq2057
    | exact resolve eq2057 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq2093 : (τ (σ y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2083
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq2083
    | exact resolve eq2083 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083
  have eq2121 : (σ y) = (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq2093 eq35
    | exact resolve eq35 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093
  have eq2136 : (σ y) = (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2121
       have i₂ := eq15 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq15 eq2121
    | exact resolve eq2121 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121
  have eq2152 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2136
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq2136
    | exact resolve eq2136 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2136
  have eq2160 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2152
    | exact resolve eq2152 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2152
  have eq2222 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2160 eq305
    | exact resolve eq305 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160
  have eq2257 : (M.op x y) = (τ (k (σ x) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2222 eq36
    | exact resolve eq36 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2259 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (k (σ x) (σ y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq2222 eq56
    | exact resolve eq56 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2272 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (k (σ x) (σ y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2259 x
       have i₂ := eq52 (k sF4 sF5) x
       grind)
    | exact superpose eq52 eq2259
    | exact resolve eq2259 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq2259
  have eq2274 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2257
       have i₂ := eq203 sF5 sF4
       grind)
    | exact superpose eq203 eq2257
    | exact resolve eq2257 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257
  have eq2281 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (k (τ (σ x)) (τ (σ y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2272 X0
       have i₂ := eq203 sF5 sF4
       grind)
    | exact superpose eq203 eq2272
    | exact resolve eq2272 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272
  have eq8114 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X1 (M.op X1 X0))) (τ (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq203 (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))
       have i₂ := eq1485 X1 X0
       grind)
    | exact superpose eq1485 eq203
    | exact resolve eq203 eq1485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8234 : (τ (σ x)) = (k (τ (M.op (σ y) (k (σ y) (σ y)))) (τ (M.op (σ y) (k (σ y) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq167 eq8114
    | exact resolve eq8114 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq8281 : (τ (σ x)) = (k (τ (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) (τ (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq8234
       have i₂ := eq448 sF5 sF5
       grind)
    | exact superpose eq448 eq8234
    | exact resolve eq8234 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8234
  have eq8330 : (τ (σ x)) = (k (k (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) (k (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq8281
       have i₂ := eq203 (M.op sF5 sF5) (M.op sF5 sF5)
       grind)
    | exact superpose eq203 eq8281
    | exact resolve eq8281 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8281
  have eq8373 : (τ (σ x)) = (k (k (τ (k (σ y) (σ y))) (τ (k (σ y) (σ y)))) (k (τ (k (σ y) (σ y))) (τ (k (σ y) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq8330
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq8330
    | exact resolve eq8330 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8330
  have eq8409 : (τ (σ x)) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq8373
       have i₂ := eq203 sF5 sF5
       grind)
    | exact superpose eq203 eq8373
    | exact resolve eq8373 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8373
  have eq8437 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq637 eq8409
    | exact resolve eq8409 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8409
  have eq8506 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq8437 eq33
    | exact resolve eq33 eq8437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8516 : (k (σ y) (σ y)) ≠ (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  have eq8899 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq8437 eq1764
    | (have r₁ := eq1764
       have r₂ := eq8437
       grind)
    | exact resolve eq1764 eq8437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764 eq8437
  have eq8903 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq8899
  have eq11406 : (τ (σ x)) = (k (τ (M.op (σ y) (k (σ y) (σ y)))) (τ (M.op (σ y) (k (σ y) (σ y))))) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq8903 eq8114
    | exact resolve eq8114 eq8903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8114 eq8903
  have eq11409 : (τ (σ x)) = (k (τ (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) (τ (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq11406
       have i₂ := eq448 sF5 sF5
       grind)
    | exact superpose eq448 eq11406
    | exact resolve eq11406 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11406
  have eq11429 : (τ (σ x)) = (k (k (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) (k (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y))))) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq11409
       have i₂ := eq203 (M.op sF5 sF5) (M.op sF5 sF5)
       grind)
    | exact superpose eq203 eq11409
    | exact resolve eq11409 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11409
  have eq11443 : (τ (σ x)) = (k (k (τ (k (σ y) (σ y))) (τ (k (σ y) (σ y)))) (k (τ (k (σ y) (σ y))) (τ (k (σ y) (σ y))))) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq11429
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq11429
    | exact resolve eq11429 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11429
  have eq11448 : (τ (σ x)) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq11443
       have i₂ := eq203 sF5 sF5
       grind)
    | exact superpose eq203 eq11443
    | exact resolve eq11443 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11443
  have eq11449 : (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq637 eq11448
    | exact resolve eq11448 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11448
  have eq11450 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq11449
  have eq11454 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq11450 eq33
    | exact resolve eq33 eq11450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11450
  have eq11560 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2222 eq11454
    | (have r₁ := eq11454
       have r₂ := eq2222
       grind)
    | exact resolve eq11454 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11454
  have eq11563 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq11560
  have eq11564 : (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq11563
  have eq11572 : (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11564 eq203
    | exact resolve eq203 eq11564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11933 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq11572 eq2281
    | exact resolve eq2281 eq11572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2281
  have eq11947 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq11933 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11933
  have eq12495 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (τ (σ y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq11947 eq15
    | exact resolve eq15 eq11947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12508 : (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11947 eq2274
    | exact resolve eq2274 eq11947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274
  have eq12517 : (τ (σ y)) = (k (τ (σ x)) (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11947 eq11572
    | exact resolve eq11572 eq11947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11572 eq11947
  have eq12562 : (τ (σ y)) = (k (τ (σ x)) (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq12517
  have eq12567 : (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq12508
  have eq12591 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12495 X0
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq12495
    | exact resolve eq12495 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12495
  have eq12594 : ∀ X0 : G, (k (σ X0) (σ y)) = (k (σ X0) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12591 X0
       have i₂ := eq15 X0 sF2
       grind)
    | exact superpose eq15 eq12591
    | exact resolve eq12591 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12591
  have eq12595 : ∀ X0 : G, (k (σ X0) (σ y)) = (k (σ X0) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq12594
    | (have j0 := eq12594 X0
       grind)
    | exact resolve eq12594 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12594
  have eq12723 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12567 eq15
    | exact resolve eq15 eq12567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12567
  have eq12739 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq12723
    | exact resolve eq12723 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12723
  have eq12744 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq12739
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq12739
    | exact resolve eq12739 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12739
  have eq12762 : (σ (σ (M.op x y))) = (k (σ (σ x)) (σ (σ (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12744 eq15
    | exact resolve eq15 eq12744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12744
  have eq12904 : (σ y) = (σ (k (τ (σ x)) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12562 eq35
    | exact resolve eq35 eq12562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12562
  have eq12918 : (σ y) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq12904
       have i₂ := eq15 (τ sF4) sF2
       grind)
    | exact superpose eq15 eq12904
    | exact resolve eq12904 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12904
  have eq12939 : (σ y) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq12918
    | exact resolve eq12918 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12918
  have eq12945 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq12939
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq12939
    | exact resolve eq12939 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12939
  have eq12967 : (σ (σ y)) = (k (σ (σ x)) (σ (σ (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12945 eq15
    | exact resolve eq15 eq12945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12945
  have eq16252 : ∀ X0 : G, (k (k (σ x) (σ (M.op x y))) X0) = (τ (k (σ (σ (M.op x y))) (σ X0))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq12762 eq48
    | exact resolve eq48 eq12762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12762
  have eq16285 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (k (σ x) (σ (M.op x y))) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16252 x
       have i₂ := eq46 sF3 x
       grind)
    | exact superpose eq46 eq16252
    | exact resolve eq16252 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16252
  have eq16305 : ∀ X0 : G, (k (k (σ x) (σ (M.op x y))) X0) = (τ (k (σ (σ y)) (σ X0))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq12967 eq48
    | exact resolve eq48 eq12967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq12967
  have eq16340 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ x) (σ (M.op x y))) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16305 x
       have i₂ := eq46 sF5 x
       grind)
    | exact superpose eq46 eq16305
    | exact resolve eq16305 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq16305
  have eq19066 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12595 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq12595
    | exact resolve eq12595 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12595
  have eq23396 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (k (σ x) (σ (M.op x y))) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16285 eq19066
    | exact resolve eq19066 eq16285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16285 eq19066
  have eq23399 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (k (σ x) (σ (M.op x y))) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq23396
  have eq26748 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq23399 eq16340
    | exact resolve eq16340 eq23399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16340 eq23399
  have eq26771 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq26748
  have eq26831 : (k (M.op x y) (M.op x y)) = (τ (k (σ y) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26771 eq72
    | exact resolve eq72 eq26771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq27001 : (k (M.op x y) (M.op x y)) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq26831
       have i₂ := eq203 sF5 sF5
       grind)
    | exact superpose eq203 eq26831
    | exact resolve eq26831 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26831
  have eq29931 : (k (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq27001 eq109
    | exact resolve eq109 eq27001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq27001
  have eq30038 : (k (M.op x y) (M.op x y)) = (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq29931
       have i₂ := eq448 (τ sF4) sF2
       grind)
    | exact superpose eq448 eq29931
    | exact resolve eq29931 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29931
  have eq30054 : (k (M.op x y) (M.op x y)) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq623 eq30038
    | exact resolve eq30038 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq30038
  have eq30059 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq637 eq30054
    | exact resolve eq30054 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq30054
  have eq30135 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30059 eq35
    | exact resolve eq35 eq30059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30059
  have eq30153 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq30135
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq30135
    | exact resolve eq30135 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30135
  have eq30189 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq30153
    | exact resolve eq30153 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30153
  have eq31263 : (σ y) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30189 eq26771
    | exact resolve eq26771 eq30189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26771 eq30189
  have eq31335 : (σ y) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq31263
  have eq31846 : (σ y) ≠ (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq31335 eq8516
    | exact resolve eq8516 eq31335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8516 eq31335
  have eq31914 : (σ y) ≠ (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq31846
  have eq31944 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq31914
       have r₂ := eq11564
       grind)
    | exact resolve eq31914 eq11564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11564 eq31914
  have eq32406 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq31944 eq33
    | exact resolve eq33 eq31944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31944
  have eq32460 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have r₁ := eq32406
       have r₂ := eq2222
       grind)
    | exact resolve eq32406 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222 eq32406
  have eq32493 : (σ y) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32460 eq1485
    | exact resolve eq1485 eq32460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32460
  have eq32526 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq32493
       have i₂ := eq83 sF3
       grind)
    | exact superpose eq83 eq32493
    | exact resolve eq32493 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32493
  have eq32918 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32526 eq1534
    | exact resolve eq1534 eq32526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534 eq32526
  have eq33056 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32918 eq36
    | exact resolve eq36 eq32918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq33104 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32918 eq8506
    | (have r₁ := eq8506
       have r₂ := eq32918
       grind)
    | exact resolve eq8506 eq32918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8506
  have eq33246 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq33104
  have eq33247 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq33246
  have eq33303 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq33056
       have i₂ := eq203 sF5 sF5
       grind)
    | exact superpose eq203 eq33056
    | exact resolve eq33056 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq33056
  have eq33514 : (σ y) = (k (M.op (σ x) (k (σ x) (σ y))) (M.op (σ x) (k (σ x) (σ y)))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33247 eq1502
    | exact resolve eq1502 eq33247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502 eq33247
  have eq33610 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33303 eq1755
    | (have r₁ := eq1755
       have r₂ := eq33303
       grind)
    | exact resolve eq1755 eq33303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq33618 : (τ (σ y)) = (M.op (τ (σ y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33303 eq305
    | exact resolve eq305 eq33303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq33303
  have eq33665 : (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq33610
  have eq33684 : (τ (σ y)) = (k (M.op (τ (σ y)) (M.op x y)) (M.op (τ (σ y)) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq33618
       have i₂ := eq448 (τ sF5) sF2
       grind)
    | exact superpose eq448 eq33618
    | exact resolve eq33618 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448 eq33618
  have eq255135 : (σ (τ (σ y))) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33665 eq15
    | exact resolve eq15 eq33665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33665
  have eq255178 : (σ y) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq255135
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq255135
    | exact resolve eq255135 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255135
  have eq255188 : (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq255178
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq255178
    | exact resolve eq255178 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255178
  have eq255411 : (τ (σ x)) = (k (M.op (τ (σ y)) (M.op x y)) (M.op (τ (σ y)) (M.op x y))) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq255188 eq1485
    | exact resolve eq1485 eq255188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485 eq255188
  have eq2143011 : (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq255411 eq33684
    | exact resolve eq33684 eq255411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33684 eq255411
  have eq2143017 : (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq2143011
  have eq2143039 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq2143017 eq33514
    | exact resolve eq33514 eq2143017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33514 eq2143017
  have eq2143106 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq2143039
  have eq2143134 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq2143106
    | exact resolve eq2143106 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143106
  have eq2143260 : (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq2143134 eq303
    | exact resolve eq303 eq2143134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq2143357 : (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq2143260
    | exact resolve eq2143260 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143260
  have eq2143378 : (σ y) = (σ (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2143357 eq35
    | exact resolve eq35 eq2143357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143357
  have eq2143380 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2143378
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2143378
    | exact resolve eq2143378 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143378
  have eq2143400 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2143380 eq33
    | exact resolve eq33 eq2143380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2143549 : (σ y) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2143380 eq2143134
    | exact resolve eq2143134 eq2143380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143134 eq2143380
  have eq2143649 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32918 eq2143400
    | exact resolve eq2143400 eq32918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32918 eq2143400
  have eq2143684 : (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq2143649
       have r₂ := eq2143549
       grind)
    | exact resolve eq2143649 eq2143549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143549 eq2143649
  have eq2143869 : (σ y) = (σ (τ (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2143684 eq35
    | exact resolve eq35 eq2143684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143684
  have eq2143878 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2143869
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2143869
    | exact resolve eq2143869 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143869
  have eq2143879 : (σ x) = (σ y) := by grind
  clear eq2143878
  have eq2143882 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2143879 eq32
    | exact resolve eq32 eq2143879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq2143883 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq2143879 eq42
    | exact resolve eq42 eq2143879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2143879
  have eq2143951 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq2143883
       have i₂ := eq83 (τ sF4)
       grind)
    | exact superpose eq83 eq2143883
    | exact resolve eq2143883 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143883
  have eq2143952 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2143882
       have i₂ := eq83 sF4
       grind)
    | exact superpose eq83 eq2143882
    | exact resolve eq2143882 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq2143882
  have eq2143979 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq2143952 eq33
    | exact resolve eq33 eq2143952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq2143952
  have eq2144394 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) := by
    first
    | exact superpose eq2143951 eq15
    | exact resolve eq15 eq2143951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143951
  have eq2144422 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2144394
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2144394
    | exact resolve eq2144394 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq2144394
  have eq2144796 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2144422 eq26
    | exact resolve eq26 eq2144422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2144422
  have eq2144857 : False := by grind
  exact eq2144857

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pxy_pyx_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq70 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq44
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq44 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) := by
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
  have eq98 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq118 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq118 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq118 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq118 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq124 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq119 sF2
       grind)
    | exact superpose eq119 eq49
    | exact resolve eq49 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq125 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq124
       have i₂ := eq119 x
       grind)
    | exact superpose eq119 eq124
    | exact resolve eq124 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq124
  have eq1470 : y = (M.op y (M.op (M.op y x) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq14
    | exact resolve eq14 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1472 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1470
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1470
    | exact resolve eq1470 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1537 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq1472 eq70
    | (have j0 := eq70 (σ x) (σ y)
       grind)
    | exact resolve eq70 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1472
  have eq1538 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq1537
    | exact resolve eq1537 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq1541 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq1538
       have r₂ := eq27
       grind)
    | exact resolve eq1538 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1561 : (σ y) = (M.op (σ y) (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x)))) ∨ x = y := by
    first
    | exact superpose eq1541 eq14
    | exact resolve eq14 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541
  have eq1563 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1561
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq1561
    | exact resolve eq1561 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq1569 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1563 eq29
    | exact resolve eq29 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1563
  have eq1597 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq1569
    | exact resolve eq1569 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1569
  have eq1598 : x = y := by grind
  clear eq1597
  have eq1659 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1598
       grind)
    | exact superpose eq1598 eq18
    | exact resolve eq18 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1660 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1598
       grind)
    | exact superpose eq1598 eq24
    | exact resolve eq24 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1598
  have eq1701 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1660
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1660
    | exact resolve eq1660 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1660
  have eq1710 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1701 eq26
    | exact resolve eq26 eq1701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1701
  have eq1846 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1710 eq125
    | exact resolve eq125 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq1710
  have eq1866 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1846
       have i₂ := eq1659
       grind)
    | exact superpose eq1659 eq1846
    | exact resolve eq1846 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659 eq1846
  have eq1869 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1866 eq15
    | exact resolve eq15 eq1866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866
  have eq1900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1869
    | exact resolve eq1869 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1869
  have eq1905 : False := by grind
  exact eq1905

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyy_x_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k (M.op (M.op X1 X0) (M.op X1 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq80 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq81 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq16
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq90 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq80
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq103
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq81
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq16
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq107
  have eq232 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq336 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq232
    | (have j0 := eq232 X0 (M.op x y)
       grind)
    | exact resolve eq232 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq523 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq531 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq529
       have i₂ := eq52 sF4 sF4
       grind)
    | exact superpose eq52 eq529
    | exact resolve eq529 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq539 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq526
       have i₂ := eq52 sF0 sF0
       grind)
    | exact superpose eq52 eq526
    | exact resolve eq526 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq541 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 X1
       have i₂ := eq52 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq52 eq523
    | exact resolve eq523 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq546 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq541 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq541
    | exact resolve eq541 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq547 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq531 X2 (M.op X0 X1)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq531
    | exact resolve eq531 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq531 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq531 (M.op X0 X0) X0
       grind)
    | exact superpose eq531 eq531
    | exact resolve eq531 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq537 eq52
    | exact resolve eq52 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq564
       have i₂ := eq52 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq52 eq564
    | exact resolve eq564 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq570 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq569
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq569
    | exact resolve eq569 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq571 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq570
       have i₂ := eq52 sF3 sF3
       grind)
    | exact superpose eq52 eq570
    | exact resolve eq570 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq572 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k (M.op X1 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq63
    | (have j0 := eq63 X0 X1
       grind)
    | (have r₁ := eq63 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 (M.op X0 X0))
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq63 (M.op X1 (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq63 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq573 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq571 eq531
    | exact resolve eq531 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq572 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq589 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq539 eq52
    | exact resolve eq52 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq589
       have i₂ := eq52 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq52 eq589
    | exact resolve eq589 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq595 : (M.op x (M.op x y)) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq594
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq594
    | exact resolve eq594 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq596 : (M.op x (M.op x y)) = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq595
       have i₂ := eq52 y y
       grind)
    | exact superpose eq52 eq595
    | exact resolve eq595 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq649 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq88 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq672 : ∀ X0 : G, (k (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (τ X0) (M.op (τ X0) (τ X0)))
       have i₂ := eq588 (τ X0)
       grind)
    | exact superpose eq588 eq38
    | exact resolve eq38 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq588
  have eq677 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq677
    | exact resolve eq677 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq681 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq678
       have r₂ := eq27
       grind)
    | exact resolve eq678 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq683 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq681
    | exact resolve eq681 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq685 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq683
    | exact resolve eq683 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq687 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq685 eq27
    | exact resolve eq27 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq685 eq573
    | exact resolve eq573 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq694 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  have eq697 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq692
    | exact resolve eq692 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq706 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq697 eq14
    | exact resolve eq14 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq709 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq571 eq706
    | exact resolve eq706 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq740 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq709 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq709
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq709
       grind)
    | exact resolve eq12 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq743 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq740
  have eq744 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq743
  have eq768 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq685 eq744
    | exact resolve eq744 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq744
  have eq773 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq768
  have eq774 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq773
       have r₂ := eq694
       grind)
    | exact resolve eq773 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq773
  have eq857 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq774 eq106
    | exact resolve eq106 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq858 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq774 eq87
    | exact resolve eq87 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq774
  have eq861 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq857
  have eq865 : y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq858
    | exact resolve eq858 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq858
  have eq866 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq861
       have r₂ := eq687
       grind)
    | exact resolve eq861 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq861
  have eq869 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq865
       have r₂ := eq70
       grind)
    | exact resolve eq865 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq865
  have eq874 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq866 eq537
    | exact resolve eq537 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq866
  have eq879 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq874
       have i₂ := eq531 sF2 sF2
       grind)
    | exact superpose eq531 eq874
    | exact resolve eq874 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq926 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq80
    | exact resolve eq80 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq869
  have eq931 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq926
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq926
    | exact resolve eq926 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq997 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq931 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq998 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq997
  have eq1002 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq998
    | exact resolve eq998 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1005 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1002
    | exact resolve eq1002 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1006 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1005
  have eq1009 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1006 eq27
    | exact resolve eq27 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq2351 : (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (M.op x (M.op y (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))))) := by
    first
    | exact superpose eq50 eq546
    | exact resolve eq546 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq2457 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op x (M.op y (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))))) := by
    first
    | (have i₁ := eq2351
       have i₂ := eq52 sF0 sF0
       grind)
    | exact superpose eq52 eq2351
    | exact resolve eq2351 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq2351
  have eq2477 : (M.op x (M.op y (M.op y y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq539 eq2457
    | exact resolve eq2457 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq2457
  have eq2489 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq2477
       have i₂ := eq596
       grind)
    | exact superpose eq596 eq2477
    | exact resolve eq2477 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477
  have eq2995 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq90 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq90
    | (have j0 := eq90 y
       grind)
    | exact resolve eq90 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq3006 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq2995
  have eq3012 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3006
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq3006
    | exact resolve eq3006 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq3006
  have eq3020 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3012
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq3012 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3012
  have eq4787 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (τ (k X0 (σ (M.op x y))))) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (τ X0))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq336 eq649
    | (have j0 := eq649 (M.op x y) (τ X0)
       grind)
    | exact resolve eq649 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq649
  have eq4895 : ∀ X0 : G, (σ (M.op x y)) ≠ (k X0 (σ (M.op x y))) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (τ X0))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4787 X0
       have i₂ := eq15 (k X0 sF1)
       grind)
    | exact superpose eq15 eq4787
    | (have j0 := eq4787 X0
       grind)
    | exact resolve eq4787 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4787
  have eq4931 : ∀ X0 : G, (σ (M.op x y)) ≠ (k X0 (σ (M.op x y))) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (τ X0))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq20 eq4895
    | (have j0 := eq4895 X0
       grind)
    | exact resolve eq4895 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4895
  have eq4962 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) ≠ (k X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4931 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4931
    | (have j0 := eq4931 X0
       grind)
    | exact resolve eq4931 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4931
  have eq4991 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) ≠ (k X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq20 eq4962
    | (have j0 := eq4962 X0
       grind)
    | exact resolve eq4962 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4962
  have eq5019 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) ≠ (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq4991 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4991
    | (have j0 := eq4991 X0
       grind)
    | exact resolve eq4991 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4991
  have eq5028 : ∀ X0 : G, (σ (M.op x y)) ≠ (k X0 (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq20 eq5019
    | (have j0 := eq5019 X0
       grind)
    | exact resolve eq5019 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5019
  have eq7419 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3020 eq112
    | exact resolve eq112 eq3020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq23288 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3020 eq113
    | exact resolve eq113 eq3020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq3020
  have eq29749 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq547 y y X0
       have i₂ := eq596
       grind)
    | exact superpose eq596 eq547
    | exact resolve eq547 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq29763 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq571 eq547
    | exact resolve eq547 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq571
  have eq32551 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq23288
       grind)
    | exact superpose eq23288 eq16
    | exact resolve eq16 eq23288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716524 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq879 eq7419
    | exact resolve eq7419 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq717456 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq716524
    | exact resolve eq716524 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716524
  have eq892396 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7419 eq32551
    | exact resolve eq32551 eq7419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32551
  have eq892397 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq892396
       have r₂ := eq13 y y
       grind)
    | exact resolve eq892396 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892396
  have eq897975 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq892397
       have i₂ := eq717456
       grind)
    | exact superpose eq717456 eq892397
    | exact resolve eq892397 eq717456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717456
  have eq898398 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq548 y
       have i₂ := eq897975
       grind)
    | exact superpose eq897975 eq548
    | exact resolve eq548 eq897975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897975
  have eq898529 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq898398
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq898398
    | exact resolve eq898398 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898398
  have eq898530 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq898529
  have eq898550 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq898530 eq20
    | exact resolve eq20 eq898530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898530
  have eq899002 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq898550
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq898550
    | exact resolve eq898550 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898550
  have eq899101 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq899002 eq1009
    | (have r₁ := eq1009
       have r₂ := eq899002
       grind)
    | exact resolve eq1009 eq899002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009 eq899002
  have eq902224 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq899101
  have eq902225 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq902224
  have eq902599 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq902225 eq29763
    | exact resolve eq29763 eq902225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29763 eq902225
  have eq904605 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq902599 x
       have i₂ := eq531 x sF2
       grind)
    | exact superpose eq531 eq902599
    | exact resolve eq902599 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902599
  have eq907268 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq904605 eq7419
    | exact resolve eq7419 eq904605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7419 eq904605
  have eq907782 : (τ (σ x)) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq907268
       have i₂ := eq892397
       grind)
    | exact superpose eq892397 eq907268
    | exact resolve eq907268 eq892397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892397 eq907268
  have eq907793 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq907782
    | exact resolve eq907782 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq907782
  have eq910173 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq548 y
       have i₂ := eq907793
       grind)
    | exact superpose eq907793 eq548
    | exact resolve eq548 eq907793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907793
  have eq910312 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq910173
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq910173
    | exact resolve eq910173 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq910173
  have eq910313 : x = (M.op x y) := by grind
  clear eq910312
  have eq910362 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq910313 eq20
    | exact resolve eq20 eq910313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq910364 : y = (M.op x (M.op x x)) := by
    first
    | exact superpose eq910313 eq50
    | exact resolve eq50 eq910313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq910577 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x x))) := by
    intro X0
    first
    | exact superpose eq910313 eq29749
    | exact resolve eq29749 eq910313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29749
  have eq910599 : x = (M.op y y) := by
    first
    | (have i₁ := eq910577 x
       have i₂ := eq531 x x
       grind)
    | exact superpose eq531 eq910577
    | exact resolve eq910577 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq910577
  have eq910746 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq910362
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq910362
    | exact resolve eq910362 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910362
  have eq910755 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq910746 eq26
    | exact resolve eq26 eq910746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq912484 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq23288
       have i₂ := eq910599
       grind)
    | exact superpose eq910599 eq23288
    | exact resolve eq23288 eq910599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23288
  have eq912636 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq912484
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq912484
    | exact resolve eq912484 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912484
  have eq912664 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq910746 eq912636
    | exact resolve eq912636 eq910746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912636
  have eq916521 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq912664 eq548
    | exact resolve eq548 eq912664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq912664
  have eq916611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq910755 eq916521
    | exact resolve eq916521 eq910755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916521
  have eq916646 : x = y := by
    first
    | (have r₁ := eq916611
       have r₂ := eq27
       grind)
    | exact resolve eq916611 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916611
  have eq917920 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq916646
       grind)
    | exact superpose eq916646 eq24
    | exact resolve eq24 eq916646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918268 : x = (M.op x x) := by
    first
    | (have i₁ := eq910599
       have i₂ := eq916646
       grind)
    | exact superpose eq916646 eq910599
    | exact resolve eq910599 eq916646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910599 eq916646
  have eq918491 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq917920
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq917920
    | exact resolve eq917920 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917920
  have eq918654 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq910746 eq918491
    | exact resolve eq918491 eq910746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918491
  have eq921516 : (σ (M.op x y)) ≠ (σ (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))) ∨ (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))))) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) := by
    first
    | (have i₁ := eq5028 (σ (M.op (τ sF1) (M.op (τ sF1) (τ sF1))))
       have i₂ := eq672 sF1
       grind)
    | exact superpose eq672 eq5028
    | (have j0 := eq5028 (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))
       grind)
    | exact resolve eq5028 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq5028
  have eq921531 : (σ (M.op x y)) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))))) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) := by
    first
    | exact superpose eq30 eq921516
    | exact resolve eq921516 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921516
  have eq921534 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))))) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) := by
    first
    | exact superpose eq910313 eq921531
    | exact resolve eq921531 eq910313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921531
  have eq921537 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))))) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) := by
    first
    | (have i₁ := eq921534
       have i₂ := eq918268
       grind)
    | exact superpose eq918268 eq921534
    | exact resolve eq921534 eq918268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918268 eq921534
  have eq921540 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))))) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) := by
    first
    | (have i₁ := eq921537
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq921537
    | exact resolve eq921537 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq921537
  have eq921543 : (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))))) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) := by
    first
    | (have r₁ := eq921540
       have r₂ := eq910746
       grind)
    | exact resolve eq921540 eq910746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910746 eq921540
  have eq921546 : (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) := by
    first
    | exact superpose eq30 eq921543
    | exact resolve eq921543 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921543
  have eq921549 : (σ (M.op x (M.op x (M.op x y)))) = (M.op (σ (M.op x y)) (σ (M.op x (M.op x (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) := by
    first
    | exact superpose eq2489 eq921546
    | exact resolve eq921546 eq2489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921546
  have eq921552 : (σ (M.op x (M.op x x))) = (M.op (σ (M.op x y)) (σ (M.op x (M.op x x)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) := by
    first
    | exact superpose eq910313 eq921549
    | exact resolve eq921549 eq910313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921549
  have eq921553 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) := by
    first
    | (have i₁ := eq921552
       have i₂ := eq910364
       grind)
    | exact superpose eq910364 eq921552
    | exact resolve eq921552 eq910364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921552
  have eq921554 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) := by
    first
    | (have i₁ := eq921553
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq921553
    | exact resolve eq921553 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921553
  have eq921555 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) := by
    first
    | exact superpose eq910755 eq921554
    | exact resolve eq921554 eq910755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921554
  have eq921556 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) := by
    first
    | exact superpose eq918654 eq921555
    | exact resolve eq921555 eq918654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918654 eq921555
  have eq921557 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) := by
    first
    | (have r₁ := eq921556
       have r₂ := eq27
       grind)
    | exact resolve eq921556 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921556
  have eq921558 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq30 eq921557
    | exact resolve eq921557 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq921557
  have eq921559 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x (M.op x (M.op x y))))) := by
    first
    | exact superpose eq2489 eq921558
    | exact resolve eq921558 eq2489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2489 eq921558
  have eq921560 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x (M.op x x)))) := by
    first
    | exact superpose eq910313 eq921559
    | exact resolve eq921559 eq910313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910313 eq921559
  have eq921561 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq921560
       have i₂ := eq910364
       grind)
    | exact superpose eq910364 eq921560
    | exact resolve eq921560 eq910364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910364 eq921560
  have eq921562 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq921561
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq921561
    | exact resolve eq921561 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq921561
  have eq921563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq910755 eq921562
    | exact resolve eq921562 eq910755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910755 eq921562
  have eq921564 : False := by grind
  exact eq921564

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxx_y_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
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
  have eq33 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq34 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0))) := by
    intro X0
    grind
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq79 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k (M.op X0 X0) X0) X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq9
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (k (M.op X0 (M.op X1 X1)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (M.op X0 X1)
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq34
    | exact resolve eq34 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq89 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq24 (M.op X1 X1) X0
       grind)
    | exact superpose eq24 eq91
    | exact resolve eq91 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq93 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq24 (M.op X1 X1) X0
       grind)
    | exact superpose eq24 eq89
    | exact resolve eq89 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq94 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq24 (M.op X1 X1) X0
       grind)
    | exact superpose eq24 eq83
    | exact resolve eq83 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq96 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (k (M.op X1 X1) X1))) := by
    intro X0 X1
    grind
  clear eq92
  have eq97 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op X0 (k (M.op X1 X1) X1)) := by
    intro X0 X1
    grind
  clear eq93
  have eq98 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (k (M.op X1 X1) X1)) := by
    intro X0 X1
    grind
  clear eq94
  have eq116 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op X1 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq35
    | exact resolve eq35 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq144 : ∀ X0 : G, (M.op (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (k (M.op X0 X0) X0) (M.op X0 X0))) = (k (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq151 : ∀ X0 : G, (M.op (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (k (M.op X0 X0) X0) (M.op X0 X0))) = (M.op (k (M.op X0 X0) X0) (k (k (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq24 (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq24
    | exact resolve eq24 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq16
    | (have j1 := eq59 y x
       grind)
    | exact resolve eq16 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq303 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq79 (σ X0)
       grind)
    | exact superpose eq79 eq23
    | exact resolve eq23 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq63 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq401 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq400 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq404 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq401 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq401
    | (have j0 := eq401 X0
       grind)
    | exact resolve eq401 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq420 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq183
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq183
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq183 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq421 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq420
  have eq422 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq79 X1
       grind)
    | exact superpose eq79 eq96
    | exact resolve eq96 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq496 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq422 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq422
    | exact resolve eq422 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq496 X0 X1
       have i₂ := eq86 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq86 eq496
    | exact resolve eq496 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq599 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X1 (M.op X1 X0)) (k X0 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1 (M.op X1 X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq680 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq79 X1
       grind)
    | exact superpose eq79 eq97
    | exact resolve eq97 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq687 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq404 X0
       grind)
    | exact superpose eq404 eq10
    | (have j1 := eq404 X0
       grind)
    | exact resolve eq10 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq706 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq79 X1
       grind)
    | exact superpose eq79 eq98
    | exact resolve eq98 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1299 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq79 (τ X0)
       have i₂ := eq687 X0
       grind)
    | exact superpose eq687 eq79
    | (have j1 := eq687 X0
       grind)
    | exact resolve eq79 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq1315 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1299 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq1299
    | (have j0 := eq1299 X0
       grind)
    | exact resolve eq1299 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1299
  have eq1316 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1315 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1370 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1316 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1316
    | exact resolve eq1316 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1385 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1 (τ X0)
       have i₂ := eq1316 X0
       grind)
    | exact superpose eq1316 eq86
    | exact resolve eq86 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1414 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq1370 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq1370
    | exact resolve eq1370 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1370
  have eq1419 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1414 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1414
    | exact resolve eq1414 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq1496 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1419 (σ X0)
       grind)
    | exact superpose eq1419 eq15
    | exact resolve eq15 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1514 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1496 X0
       have i₂ := eq1419 X0
       grind)
    | exact superpose eq1419 eq1496
    | exact resolve eq1496 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1578 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1 (σ X0)
       have i₂ := eq1514 X0
       grind)
    | exact superpose eq1514 eq86
    | exact resolve eq86 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1656 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1385 X0 X1
       have i₂ := eq1419 X0
       grind)
    | exact superpose eq1419 eq1385
    | exact resolve eq1385 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385 eq1419
  have eq1741 : ∀ X0 X1 : G, (τ (k (M.op X0 X0) X0)) = (M.op X1 (M.op X1 (τ (k (k (M.op X0 X0) X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1656 (k (M.op X0 X0) X0) X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq1656
    | exact resolve eq1656 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1656
  have eq1782 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op X1 (τ (k (M.op X0 (M.op X0 X0)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1741 X0 X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq1741
    | exact resolve eq1741 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741
  have eq1803 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op X1 (τ (M.op X0 (M.op X0 (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1782 X0 X1
       have i₂ := eq680 X0 X0
       grind)
    | exact superpose eq680 eq1782
    | exact resolve eq1782 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782
  have eq1820 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (τ X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1803 X0 X1
       have i₂ := eq86 X0 X0
       grind)
    | exact superpose eq86 eq1803
    | exact resolve eq1803 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803
  have eq2174 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X0 (M.op X1 (M.op X1 X1))) (M.op X0 (M.op X1 (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 X1
       have i₂ := eq680 X0 X1
       grind)
    | exact superpose eq680 eq116
    | exact resolve eq116 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq2175 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2174 X0 X1
       have i₂ := eq24 (M.op X1 (M.op X1 X1)) X0
       grind)
    | exact superpose eq24 eq2174
    | exact resolve eq2174 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq2176 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op (M.op X1 X1) (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2175 X0 X1
       have i₂ := eq24 (M.op X1 X1) X1
       grind)
    | exact superpose eq24 eq2175
    | exact resolve eq2175 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq2177 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2176 X0 X1
       have i₂ := eq9 X1 X1
       grind)
    | exact superpose eq9 eq2176
    | exact resolve eq2176 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176
  have eq2255 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2177 X0 (M.op X1 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq2177
    | exact resolve eq2177 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177
  have eq2999 : ∀ X0 : G, (k (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (k (M.op X0 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq144 X0
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq144
    | exact resolve eq144 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq3000 : ∀ X0 : G, (k (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq2999 x
       have i₂ := eq680 x x
       grind)
    | exact superpose eq680 eq2999
    | exact resolve eq2999 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2999
  have eq3001 : ∀ X0 : G, (k (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3000 X0
       have i₂ := eq24 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq24 eq3000
    | exact resolve eq3000 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3000
  have eq3002 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3001 X0
       have i₂ := eq9 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq3001
    | exact resolve eq3001 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3001
  have eq3003 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3002 X0
       have i₂ := eq86 X0 X0
       grind)
    | exact superpose eq86 eq3002
    | exact resolve eq3002 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002
  have eq3450 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (k (M.op X0 (M.op X0 X0)) (M.op X0 X0))) = (M.op (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (k (M.op X0 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq151 X0
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq151
    | exact resolve eq151 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq3451 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3450 x
       have i₂ := eq680 x x
       grind)
    | exact superpose eq680 eq3450
    | exact resolve eq3450 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq3450
  have eq3452 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3451 X0
       have i₂ := eq24 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq24 eq3451
    | exact resolve eq3451 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3451
  have eq3453 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3452 X0
       have i₂ := eq9 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq3452
    | exact resolve eq3452 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3452
  have eq3454 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq3453 X0
       have i₂ := eq86 X0 X0
       grind)
    | exact superpose eq86 eq3453
    | exact resolve eq3453 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq3453
  have eq4623 : ∀ X0 X1 : G, (τ (M.op (M.op (σ X0) (M.op (σ X0) (σ X0))) (M.op (M.op (σ X0) (M.op (σ X0) (σ X0))) (M.op (σ X0) (M.op (σ X0) (σ X0)))))) = (M.op X1 (M.op X1 (k (τ (M.op (σ X0) (σ X0))) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1820 (M.op (σ X0) (M.op (σ X0) (σ X0))) X1
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq1820
    | exact resolve eq1820 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4680 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (τ (σ X1)))) = (k (τ (M.op (σ X1) (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X1
       have i₂ := eq1820 (σ X1) X0
       grind)
    | exact superpose eq1820 eq303
    | exact resolve eq303 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq4682 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (M.op X0 (M.op X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 (M.op X1 X1))
       have i₂ := eq1820 X1 X0
       grind)
    | exact superpose eq1820 eq11
    | exact resolve eq11 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq4719 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (τ (σ X1)))) = (k (τ (σ (M.op X1 X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4680 X0 X1
       have i₂ := eq1514 X1
       grind)
    | exact superpose eq1514 eq4680
    | exact resolve eq4680 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4680
  have eq4758 : ∀ X0 X1 : G, (τ (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (σ X0) (σ (M.op X0 X0)))))) = (M.op X1 (M.op X1 (k (τ (σ (M.op X0 X0))) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4623 X0 X1
       have i₂ := eq1514 X0
       grind)
    | exact superpose eq1514 eq4623
    | exact resolve eq4623 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4623
  have eq4769 : ∀ X0 X1 : G, (k (M.op X1 X1) X1) = (M.op X0 (M.op X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4719 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq4719
    | exact resolve eq4719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719
  have eq4802 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (k (M.op X0 X0) X0))) = (τ (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (σ X0) (σ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq4758 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4758
    | exact resolve eq4758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4758
  have eq4809 : ∀ X0 X1 : G, (k (M.op X1 X1) X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4769 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4769
    | exact resolve eq4769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4769
  have eq4831 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (k (M.op X0 X0) X0))) = (τ (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq4802 X0 X1
       have i₂ := eq24 (σ (M.op X0 X0)) (σ X0)
       grind)
    | exact superpose eq24 eq4802
    | exact resolve eq4802 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4802
  have eq4845 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (k (M.op X0 X0) X0))) = (τ (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq4831 X0 X1
       have i₂ := eq706 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact superpose eq706 eq4831
    | exact resolve eq4831 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq4831
  have eq4854 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (k (M.op X0 X0) X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4845 X0 X1
       have i₂ := eq1578 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq1578 eq4845
    | exact resolve eq4845 eq1578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578 eq4845
  have eq4858 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (k (M.op X0 X0) X0))) = (τ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4854 X0 X1
       have i₂ := eq1514 X0
       grind)
    | exact superpose eq1514 eq4854
    | exact resolve eq4854 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4854
  have eq4860 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (k (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4858 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4858
    | exact resolve eq4858 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4858
  have eq4862 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4860 X0 X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq4860
    | exact resolve eq4860 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4860
  have eq5052 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4809 X2 X1
       have i₂ := eq4809 X0 X1
       grind)
    | exact superpose eq4809 eq4809
    | exact resolve eq4809 eq4809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4809
  have eq5437 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5052 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq539 X0 X1
       grind)
    | exact superpose eq539 eq5052
    | exact resolve eq5052 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq5553 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3003 X1
       have i₂ := eq5052 X1 X1 X0
       grind)
    | (have i₁ := eq3003 X1
       have i₂ := eq5052 X0 X1 X1
       grind)
    | exact superpose eq5052 eq3003
    | exact resolve eq3003 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq5555 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3454 X1
       have i₂ := eq5052 X1 X1 X0
       grind)
    | (have i₁ := eq3454 X1
       have i₂ := eq5052 X0 X1 X1
       grind)
    | exact superpose eq5052 eq3454
    | exact resolve eq3454 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3454 eq5052
  have eq6370 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X1))
       have i₂ := eq5555 X0 X1
       grind)
    | exact superpose eq5555 eq9
    | exact resolve eq9 eq5555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5555
  have eq6418 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (k (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    grind
  clear eq6370
  have eq6477 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6418 X0 X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq6418
    | exact resolve eq6418 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6418
  have eq8344 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4682 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4682
    | exact resolve eq4682 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4682
  have eq8522 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8344 X0 X1
       have i₂ := eq1514 X0
       grind)
    | exact superpose eq1514 eq8344
    | exact resolve eq8344 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8344
  have eq12349 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq421
       have i₂ := eq1514 x
       grind)
    | exact superpose eq1514 eq421
    | exact resolve eq421 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq12355 : y = (M.op y (M.op y (M.op x (M.op x x)))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq422 y x
       have i₂ := eq12349
       grind)
    | exact superpose eq12349 eq422
    | exact resolve eq422 eq12349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422 eq12349
  have eq12371 : y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12355
       have i₂ := eq4862 x y
       grind)
    | exact superpose eq4862 eq12355
    | exact resolve eq12355 eq4862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4862 eq12355
  have eq12372 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq12371
  have eq41341 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq599 X0 X1
       have i₂ := eq5553 X1 X0
       grind)
    | exact superpose eq5553 eq599
    | exact resolve eq599 eq5553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599 eq5553
  have eq63938 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) = (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2255 (M.op X0 (M.op X0 X1)) (M.op X1 X1) X2
       have i₂ := eq41341 X1 X0
       grind)
    | exact superpose eq41341 eq2255
    | exact resolve eq2255 eq41341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2255 eq41341
  have eq64298 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X0 X1)) (k (M.op X1 X1) X1))) = (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X1)) (k (M.op X1 X1) X1))) (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    grind
  clear eq63938
  have eq64537 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X0 X1)) (M.op X1 (M.op X1 X1)))) = (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X1)) (M.op X1 (M.op X1 X1)))) (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64298 X0 X0 X2
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq64298
    | exact resolve eq64298 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq64298
  have eq64695 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X2 X1) (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64537 X1 X0 X2
       have i₂ := eq6477 X0 X1
       grind)
    | exact superpose eq6477 eq64537
    | exact resolve eq64537 eq6477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6477 eq64537
  have eq170287 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X0 (σ x))))) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq64695 X0 (σ x) (σ y)
       have i₂ := eq12372
       grind)
    | exact superpose eq12372 eq64695
    | exact resolve eq64695 eq12372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12372 eq64695
  have eq170312 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq170287 x
       have i₂ := eq5437 (σ x) x (σ y)
       grind)
    | exact superpose eq5437 eq170287
    | exact resolve eq170287 eq5437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5437 eq170287
  have eq170391 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq170312
       have i₂ := eq1514 x
       grind)
    | exact superpose eq1514 eq170312
    | exact resolve eq170312 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1514 eq170312
  have eq170392 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq170391
  have eq170520 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq170392
       grind)
    | exact superpose eq170392 eq10
    | exact resolve eq10 eq170392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170392
  have eq170749 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq170520
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq170520
    | exact resolve eq170520 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170520
  have eq170750 : y = (M.op x x) := by grind
  clear eq170749
  have eq172304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8522 x x
       have i₂ := eq170750
       grind)
    | exact superpose eq170750 eq8522
    | exact resolve eq8522 eq170750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8522 eq170750
  have eq172346 : False := by grind
  exact eq172346
