import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation2736 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq97 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq192 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq97 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 (k (σ X1) (σ X0)) (M.op (σ X0) (σ X1))
       have j1 := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq204 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq205 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq204 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq213 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq205
    | (have j0 := eq205 X0 X1
       grind)
    | exact resolve eq205 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq214 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq213 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq455 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq214 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq214
    | exact resolve eq214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq214 x y
       grind)
    | exact superpose eq214 eq16
    | (have j1 := eq214 x y
       grind)
    | exact resolve eq16 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq484 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq455 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq455
    | (have j0 := eq455 X0 X1
       grind)
    | exact resolve eq455 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq455
  have eq494 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq484
    | exact resolve eq484 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq590 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq462
       have i₂ := eq494 x y
       grind)
    | exact superpose eq494 eq462
    | (have j1 := eq494 (σ x) (σ y)
       grind)
    | (have r₁ := eq462
       have r₂ := eq494 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq462
       have r₂ := eq494 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq462 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq494
  have eq593 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq590
  have eq638 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq593
       grind)
    | exact superpose eq593 eq10
    | exact resolve eq10 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq673 : x = y ∨ x = y := by
    first
    | (have i₁ := eq638
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq638
    | exact resolve eq638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq674 : x = y := by grind
  clear eq673
  have eq676 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq674
       grind)
    | exact superpose eq674 eq16
    | exact resolve eq16 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq677 : False := by grind
  exact eq677

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation2736 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq97 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq6502 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq97 X1 X0
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq97 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq97 (M.op X1 (σ X1)) X1
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq6519 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq6502 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6502
  have eq6520 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = X1 ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq6519 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6519
  have eq13488 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6520 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6520
    | exact resolve eq6520 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6520
  have eq13616 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13488 X0 X1
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq13488
    | (have j0 := eq13488 X0 X1
       grind)
    | exact resolve eq13488 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq13488
  have eq13968 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq13616 X1 (σ X0)
       grind)
    | exact superpose eq13616 eq28
    | (have j1 := eq13616 (k X1 (σ X0)) X1
       grind)
    | exact resolve eq28 eq13616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq13976 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq13616 X1 X0
       grind)
    | exact superpose eq13616 eq11
    | (have j1 := eq13616 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq13616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13616
  have eq14103 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13976 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq13976
    | (have j0 := eq13976 X0 X1
       grind)
    | exact resolve eq13976 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13976
  have eq14174 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14103 (τ X0) X1
       grind)
    | exact superpose eq14103 eq19
    | (have j1 := eq14103 (τ X0) X1
       grind)
    | exact resolve eq19 eq14103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq14103
  have eq14645 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq13968 X1 (σ X0)
       grind)
    | exact superpose eq13968 eq37
    | (have j1 := eq13968 X0 (σ X1)
       grind)
    | exact resolve eq37 eq13968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq13968
  have eq14731 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14645 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq14645
    | (have j0 := eq14645 X0 X1
       grind)
    | exact resolve eq14645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14645
  have eq14776 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14731 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14731
    | (have j0 := eq14731 X0 X1
       grind)
    | exact resolve eq14731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14731
  have eq14792 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14776 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14776
    | (have j0 := eq14776 X0 X1
       grind)
    | exact resolve eq14776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14776
  have eq14923 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14174 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14174
    | exact resolve eq14174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14174
  have eq15021 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14923 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq14923
    | (have j0 := eq14923 X0 X1
       grind)
    | exact resolve eq14923 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14923
  have eq15366 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq14792 X0 X1
       grind)
    | exact superpose eq14792 eq11
    | (have j1 := eq14792 X0 X1
       grind)
    | exact resolve eq11 eq14792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14792
  have eq17214 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15366 y x
       grind)
    | exact superpose eq15366 eq16
    | (have j1 := eq15366 y x
       grind)
    | exact resolve eq16 eq15366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15366
  have eq17301 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq17214
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq17214
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq17214
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq17214
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq17214 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17302 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq17214
       have i₂ := eq15021 x y
       grind)
    | exact superpose eq15021 eq17214
    | (have j1 := eq15021 x y
       grind)
    | (have r₁ := eq17214
       have r₂ := eq15021 x y
       grind)
    | (have r₁ := eq17214
       have r₂ := eq15021 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq17214
       have r₂ := eq15021 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq17214 eq15021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15021 eq17214
  have eq17305 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17302
  have eq17306 : x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq17305
  have eq17307 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17301
  have eq17308 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq17307
  have eq17455 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17306
       grind)
    | exact superpose eq17306 eq16
    | exact resolve eq16 eq17306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17306
  have eq17456 : y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17455
       have r₂ := eq22 x
       grind)
    | exact resolve eq17455 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17455
  have eq17461 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq267 x y
       have i₂ := eq17456
       grind)
    | exact superpose eq17456 eq267
    | (have j0 := eq267 x y
       grind)
    | exact resolve eq267 eq17456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq17456
  have eq17478 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17461
  have eq17479 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17478
  have eq17625 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17308
       grind)
    | exact superpose eq17308 eq16
    | exact resolve eq16 eq17308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17308
  have eq17626 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17625
       have r₂ := eq22 x
       grind)
    | exact resolve eq17625 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17625
  have eq17729 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17479
       grind)
    | exact superpose eq17479 eq16
    | exact resolve eq16 eq17479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17479
  have eq17786 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17729
       have i₂ := eq17626
       grind)
    | exact superpose eq17626 eq17729
    | exact resolve eq17729 eq17626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17626 eq17729
  have eq17790 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq17786
  have eq17791 : (σ x) = (σ y) := by grind
  clear eq17790
  have eq17880 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17791
       grind)
    | exact superpose eq17791 eq16
    | exact resolve eq16 eq17791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17881 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17791
       grind)
    | exact superpose eq17791 eq10
    | exact resolve eq10 eq17791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17791
  have eq17982 : x = y := by
    first
    | (have i₁ := eq17881
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17881
    | exact resolve eq17881 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17881
  have eq17983 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17880
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq17880
    | exact resolve eq17880 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17880
  have eq17984 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17983
       have i₂ := eq17982
       grind)
    | exact superpose eq17982 eq17983
    | exact resolve eq17983 eq17982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17982 eq17983
  have eq17985 : False := by grind
  exact eq17985

/-- `Equation2739`: `x = ((y ◇ y) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_x_y_pxy_Equation2739 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2739 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2739.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) = X0 := by
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ (k X0 (k x y))) = (k (σ X0) (k (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq10
    | exact resolve eq10 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq60 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq60
    | (have j0 := eq60 x y
       grind)
    | exact resolve eq60 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq60
    | (have j0 := eq60 (σ x) (σ y)
       grind)
    | exact resolve eq60 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 (M.op X0 X1) X0
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq60
    | exact resolve eq60 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X0
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq71 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq63 eq60
    | exact resolve eq60 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : x ≠ x ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq63 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq63
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq73
  have eq76 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq64 eq14
    | exact resolve eq14 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq64 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq64
       grind)
    | exact resolve eq13 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq77
  have eq81 : (M.op x y) ≠ (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq71 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq71
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq82 : x = (k x (M.op x y)) := by grind
  clear eq81
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq108 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq109 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq113 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq82 eq46
    | exact resolve eq46 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq82
  have eq114 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq113
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq113
    | exact resolve eq113 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq118 : (σ (k y (k y x))) = (k (σ y) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq37 (k y x)
       have i₂ := eq108
       grind)
    | exact superpose eq108 eq37
    | exact resolve eq37 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq125 : (σ (k (M.op x y) (k x y))) = (k (σ (M.op x y)) (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq38 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq38
    | exact resolve eq38 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq132 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq74 eq127
    | exact resolve eq127 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq127
  have eq133 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq21 eq132
    | exact resolve eq132 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq142 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq109
       grind)
    | exact superpose eq109 eq16
    | exact resolve eq16 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq66 X0 X1
       grind)
    | exact resolve eq13 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq290 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq11 (τ X0) X1
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 (τ X0) X1
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq370 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq372 : ∀ X0 X1 : G, (σ (k y (k X0 (τ X1)))) = (k (σ y) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq37
    | exact resolve eq37 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq417 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (M.op X0 X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq76 eq70
    | exact resolve eq70 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq527 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq87 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq529 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq527 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq2340 : ∀ X0 X1 : G, (k (σ y) (k (σ X0) X1)) = (σ (k y (M.op X0 (τ X1)))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1
       have i₂ := eq11 X0 (τ X1)
       grind)
    | exact superpose eq11 eq372
    | (have j1 := eq11 X0 (τ X1)
       grind)
    | exact resolve eq372 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq3859 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq529 y
       have i₂ := eq109
       grind)
    | exact superpose eq109 eq529
    | (have j0 := eq529 y
       grind)
    | exact resolve eq529 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq3864 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3859
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3859
    | exact resolve eq3859 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3859
  have eq3870 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3864
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3864
    | exact resolve eq3864 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3864
  have eq5661 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq290 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq290
    | exact resolve eq290 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq5753 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5661 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq5661
    | (have j0 := eq5661 X0 X1
       grind)
    | exact resolve eq5661 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5661
  have eq6722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6723 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq6722
    | exact resolve eq6722 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6722
  have eq6734 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq6723
       have r₂ := eq28
       grind)
    | exact resolve eq6723 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6723
  have eq6738 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq6734
    | exact resolve eq6734 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6734
  have eq6852 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq6738 eq60
    | exact resolve eq60 eq6738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6738
  have eq6905 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq6852
    | exact resolve eq6852 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6852
  have eq6906 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6905
  have eq6915 : x = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70 y y
       have i₂ := eq6906
       grind)
    | exact superpose eq6906 eq70
    | exact resolve eq70 eq6906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6906
  have eq6962 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq6915
       have r₂ := eq51
       grind)
    | exact resolve eq6915 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq6915
  have eq6984 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq6962
       grind)
    | exact superpose eq6962 eq45
    | exact resolve eq45 eq6962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6962
  have eq6999 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6984
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6984
    | exact resolve eq6984 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6984
  have eq7004 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq6999
       have r₂ := eq52
       grind)
    | exact resolve eq6999 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq6999
  have eq7006 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq98 eq7004
    | exact resolve eq7004 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq7010 : (τ (σ x)) = (k x y) := by
    first
    | exact superpose eq7004 eq56
    | exact resolve eq56 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7018 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7004 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7019 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq7018
    | exact resolve eq7018 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7018
  have eq7026 : x = (k x y) := by
    first
    | exact superpose eq29 eq7010
    | exact resolve eq7010 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7010
  have eq7030 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq7019
    | exact resolve eq7019 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7019
  have eq7077 : (σ (k (M.op x y) (k x y))) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (k (σ x) (σ y)) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq130 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq130
    | exact resolve eq130 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq130
  have eq7136 : (σ (k (M.op x y) (k x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (k (σ x) (σ y)) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) := by
    first
    | exact superpose eq7004 eq7077
    | exact resolve eq7077 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7077
  have eq7151 : (k (σ (M.op x y)) (k (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (k (σ x) (σ y)) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) := by
    first
    | exact superpose eq125 eq7136
    | exact resolve eq7136 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq7136
  have eq7160 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (k (σ x) (σ y)) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) := by
    first
    | exact superpose eq7004 eq7151
    | exact resolve eq7151 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7151
  have eq7166 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (k (σ x) (σ y)) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) := by
    first
    | exact superpose eq133 eq7160
    | exact resolve eq7160 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq7160
  have eq7170 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) := by
    first
    | exact superpose eq7004 eq7166
    | exact resolve eq7166 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7166
  have eq7175 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq7004 eq7170
    | exact resolve eq7170 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7170
  have eq8187 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq60 y y
       have i₂ := eq7006
       grind)
    | exact superpose eq7006 eq60
    | exact resolve eq60 eq7006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7006
  have eq8200 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq8187
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8187
    | exact resolve eq8187 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8187
  have eq8201 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq8200
  have eq8204 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8201 eq29
    | exact resolve eq29 eq8201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq8221 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8201 eq114
    | exact resolve eq114 eq8201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq8201
  have eq8304 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq8204
    | exact resolve eq8204 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8204
  have eq8315 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8304 eq21
    | exact resolve eq21 eq8304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8328 : (σ (k y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8304 eq129
    | exact resolve eq129 eq8304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq8304
  have eq8399 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8328
       have i₂ := eq109
       grind)
    | exact superpose eq109 eq8328
    | exact resolve eq8328 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq8328
  have eq8406 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8315
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8315
    | exact resolve eq8315 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8315
  have eq9163 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8406 eq27
    | exact resolve eq27 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9446 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8221 eq175
    | exact resolve eq175 eq8221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq8221
  have eq9483 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq9446
    | exact resolve eq9446 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9446
  have eq13932 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9483 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq9483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9483
  have eq13944 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq13932
  have eq14339 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq7175 eq60
    | exact resolve eq60 eq7175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7175
  have eq14915 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X1)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq13944 eq14
    | exact resolve eq14 eq13944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13944
  have eq18328 : (σ y) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8399 eq3870
    | exact resolve eq3870 eq8399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3870 eq8399
  have eq28099 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7030 eq60
    | exact resolve eq60 eq7030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7030
  have eq28118 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq28099
    | exact resolve eq28099 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28099
  have eq28119 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28118
  have eq28122 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28119 eq28
    | exact resolve eq28 eq28119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28128 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28119 eq78
    | exact resolve eq78 eq28119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq28119
  have eq28207 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8406 eq28122
    | (have r₁ := eq28122
       have r₂ := eq8406
       grind)
    | exact resolve eq28122 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28122
  have eq28208 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq28207
  have eq28215 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28208 eq64
    | exact resolve eq64 eq28208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq28491 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq28215 eq14
    | exact resolve eq14 eq28215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28215
  have eq134425 : (σ (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7004 eq5753
    | (have j0 := eq5753 (σ x) (σ y)
       grind)
    | exact resolve eq5753 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5753 eq7004
  have eq135104 : (σ (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq134425
    | exact resolve eq134425 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134425
  have eq135363 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq135104
    | exact resolve eq135104 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135104
  have eq347354 : ∀ X0 : G, (k (σ y) (k (σ X0) (k (σ x) (σ y)))) = (σ (k y (M.op X0 (k x y)))) ∨ (M.op (k x y) (k x y)) = X0 ∨ (k x y) = (M.op X0 (k x y)) := by
    intro X0
    first
    | exact superpose eq56 eq2340
    | exact resolve eq2340 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq2340
  have eq347583 : ∀ X0 : G, (k (σ y) (k (σ X0) (k (σ x) (σ y)))) = (σ (k y (M.op X0 x))) ∨ (M.op (k x y) (k x y)) = X0 ∨ (k x y) = (M.op X0 (k x y)) := by
    intro X0
    first
    | (have i₁ := eq347354 X0
       have i₂ := eq7026
       grind)
    | exact superpose eq7026 eq347354
    | (have j0 := eq347354 X0
       grind)
    | exact resolve eq347354 eq7026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347354
  have eq347623 : ∀ X0 : G, (k (σ y) (σ (k X0 (k x y)))) = (σ (k y (M.op X0 x))) ∨ (M.op (k x y) (k x y)) = X0 ∨ (k x y) = (M.op X0 (k x y)) := by
    intro X0
    first
    | exact superpose eq54 eq347583
    | (have j0 := eq347583 X0
       grind)
    | exact resolve eq347583 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq347583
  have eq347651 : ∀ X0 : G, (σ (k y (k X0 (k x y)))) = (σ (k y (M.op X0 x))) ∨ (M.op (k x y) (k x y)) = X0 ∨ (k x y) = (M.op X0 (k x y)) := by
    intro X0
    first
    | exact superpose eq37 eq347623
    | (have j0 := eq347623 X0
       grind)
    | exact resolve eq347623 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq347623
  have eq347658 : ∀ X0 : G, (σ (k y (k X0 x))) = (σ (k y (M.op X0 x))) ∨ (M.op (k x y) (k x y)) = X0 ∨ (k x y) = (M.op X0 (k x y)) := by
    intro X0
    first
    | (have i₁ := eq347651 X0
       have i₂ := eq7026
       grind)
    | exact superpose eq7026 eq347651
    | (have j0 := eq347651 X0
       grind)
    | exact resolve eq347651 eq7026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347651
  have eq347665 : ∀ X0 : G, (M.op x x) = X0 ∨ (σ (k y (k X0 x))) = (σ (k y (M.op X0 x))) ∨ (k x y) = (M.op X0 (k x y)) := by
    intro X0
    first
    | (have i₁ := eq347658 X0
       have i₂ := eq7026
       grind)
    | exact superpose eq7026 eq347658
    | (have j0 := eq347658 X0
       grind)
    | exact resolve eq347658 eq7026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347658
  have eq347672 : ∀ X0 : G, x = (M.op X0 x) ∨ (M.op x x) = X0 ∨ (σ (k y (k X0 x))) = (σ (k y (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq347665 X0
       have i₂ := eq7026
       grind)
    | exact superpose eq7026 eq347665
    | (have j0 := eq347665 X0
       grind)
    | exact resolve eq347665 eq7026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7026 eq347665
  have eq412783 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq135363 eq60
    | exact resolve eq60 eq135363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135363
  have eq412873 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq412783
    | exact resolve eq412783 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412783
  have eq412874 : (σ (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq412873
  have eq412926 : ∀ X0 : G, (τ (k (σ (σ x)) X0)) = (k (M.op (σ x) (σ y)) (τ X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq412874 eq370
    | exact resolve eq370 eq412874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412874
  have eq413114 : ∀ X0 : G, (k (σ x) (τ X0)) = (k (M.op (σ x) (σ y)) (τ X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq412926 x
       have i₂ := eq370 sF2 x
       grind)
    | exact superpose eq370 eq412926
    | exact resolve eq412926 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq412926
  have eq413895 : ∀ X0 : G, (k (σ x) X0) = (k (M.op (σ x) (σ y)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq413114 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq413114
    | exact resolve eq413114 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413114
  have eq414404 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op X0 X0) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq417 eq413895
    | exact resolve eq413895 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq413895
  have eq2247212 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq14339 eq66
    | exact resolve eq66 eq14339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq14339
  have eq2247413 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq2247212
  have eq2247425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2247413 eq9163
    | exact resolve eq9163 eq2247413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9163
  have eq2247691 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2247425
       have r₂ := eq28
       grind)
    | exact resolve eq2247425 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247425
  have eq2247790 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2247691 eq70
    | exact resolve eq70 eq2247691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq2247691
  have eq2250082 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2247790 eq18328
    | exact resolve eq18328 eq2247790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18328 eq2247790
  have eq2250479 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2250082
  have eq2250487 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2250479
       have r₂ := eq8406
       grind)
    | exact resolve eq2250479 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2250479
  have eq2253540 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2250487 eq28491
    | exact resolve eq28491 eq2250487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28491 eq2250487
  have eq2253569 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2253540
  have eq2253604 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq2253569
    | exact resolve eq2253569 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253569
  have eq2261523 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28208 eq2253604
    | exact resolve eq2253604 eq28208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28208 eq2253604
  have eq2261756 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2261523
  have eq2261770 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq2261756
    | exact resolve eq2261756 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2261756
  have eq2261775 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2261770 eq28
    | exact resolve eq28 eq2261770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261770
  have eq2263109 : x = (M.op x y) := by
    first
    | (have r₁ := eq2261775
       have r₂ := eq8406
       grind)
    | exact resolve eq2261775 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8406 eq2261775
  have eq2263119 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2263109 eq21
    | exact resolve eq21 eq2263109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2263122 : x = (M.op x x) := by
    first
    | exact superpose eq2263109 eq63
    | exact resolve eq63 eq2263109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq2264772 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2263119
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2263119
    | exact resolve eq2263119 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263119
  have eq2265211 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2264772 eq28128
    | exact resolve eq28128 eq2264772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28128
  have eq2266839 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2264772 eq2247413
    | exact resolve eq2247413 eq2264772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247413
  have eq2266841 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2266839
  have eq2267027 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2265211
       have r₂ := eq28
       grind)
    | exact resolve eq2265211 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265211
  have eq2275346 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2266841 eq414404
    | exact resolve eq414404 eq2266841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414404 eq2266841
  have eq2275572 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2264772 eq2275346
    | exact resolve eq2275346 eq2264772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275346
  have eq2276139 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2275572
       have i₂ := eq278 sF1 sF1
       grind)
    | exact superpose eq278 eq2275572
    | exact resolve eq2275572 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275572
  have eq2276351 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2276139
       have r₂ := eq28
       grind)
    | exact resolve eq2276139 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276139
  have eq2276569 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq2276351 eq28
    | exact resolve eq28 eq2276351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2276351
  have eq3037320 : ∀ X0 : G, (σ (k y (k X0 x))) = (σ (k y (M.op X0 x))) ∨ x = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq347672 X0
       have i₂ := eq2263122
       grind)
    | exact superpose eq2263122 eq347672
    | (have j0 := eq347672 X0
       grind)
    | exact resolve eq347672 eq2263122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347672 eq2263122
  have eq3038049 : (k (σ y) (k (σ y) (σ x))) = (σ (k y (M.op y x))) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq118
       have i₂ := eq3037320 y
       grind)
    | exact superpose eq3037320 eq118
    | (have j1 := eq3037320 y
       grind)
    | exact resolve eq118 eq3037320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq3037320
  have eq3039027 : (σ y) = (k (σ y) (k (σ y) (σ x))) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3038049
       have i₂ := eq278 y x
       grind)
    | exact superpose eq278 eq3038049
    | exact resolve eq3038049 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq3038049
  have eq3039271 : (σ y) = (k (σ y) (k (σ y) (σ (M.op x y)))) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2264772 eq3039027
    | exact resolve eq3039027 eq2264772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3039027
  have eq3039457 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2267027 eq3039271
    | exact resolve eq3039271 eq2267027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267027 eq3039271
  have eq3039534 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3039457
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3039457
    | exact resolve eq3039457 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3039457
  have eq3072673 : (τ (σ y)) = (k y y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3039534 eq142
    | exact resolve eq142 eq3039534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq3039534
  have eq3073223 : y = (k y y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq30 eq3072673
    | exact resolve eq3072673 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3072673
  have eq3078089 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq3073223
       grind)
    | exact superpose eq3073223 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq3073223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3073223
  have eq3078214 : y = (M.op y y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq3078089
  have eq3080709 : y = (M.op (M.op (M.op x y) y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq14915 y y
       have i₂ := eq3078214
       grind)
    | exact superpose eq3078214 eq14915
    | exact resolve eq14915 eq3078214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14915 eq3078214
  have eq3080812 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2263109 eq3080709
    | exact resolve eq3080709 eq2263109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3080709
  have eq3081445 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3080812
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3080812
    | exact resolve eq3080812 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3080812
  have eq3081851 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2263109 eq3081445
    | exact resolve eq3081445 eq2263109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3081445
  have eq3082014 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3081851
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3081851
    | exact resolve eq3081851 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3081851
  have eq3082015 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq3082014
  have eq3082082 : x = y ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2263109 eq3082015
    | exact resolve eq3082015 eq2263109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3082015
  have eq3082083 : x = (M.op y x) ∨ x = y := by grind
  clear eq3082082
  have eq3082213 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq60 y x
       have i₂ := eq3082083
       grind)
    | exact superpose eq3082083 eq60
    | exact resolve eq60 eq3082083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq3082083
  have eq3082495 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3082213
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3082213
    | exact resolve eq3082213 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3082213
  have eq3082536 : x = y ∨ x = y := by
    first
    | exact superpose eq2263109 eq3082495
    | exact resolve eq3082495 eq2263109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263109 eq3082495
  have eq3082537 : x = y := by grind
  clear eq3082536
  have eq3082568 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3082537
       grind)
    | exact superpose eq3082537 eq25
    | exact resolve eq25 eq3082537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3082537
  have eq3083458 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3082568
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3082568
    | exact resolve eq3082568 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3082568
  have eq3083617 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2264772 eq3083458
    | exact resolve eq3083458 eq2264772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264772 eq3083458
  have eq3083711 : False := by grind
  exact eq3083711

/-- `Equation2739`: `x = ((y ◇ y) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_x_pxy_Equation2739 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2739 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2739.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) = X0 := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq53 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X0 X1) X0
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X1 X1) X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X2) X1 X0
       have i₂ := eq53 X0 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 X2)) ≠ X0 ∨ (M.op X0 (M.op (M.op X1 X1) (M.op X0 X2))) = (k X0 (M.op (M.op X1 X1) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 X1) (M.op X0 X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 (M.op (M.op X1 X1) (M.op X0 X2))
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq68 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : x ≠ x ∨ x = (M.op x (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq54 eq12
    | (have j0 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq54
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : x = (M.op x (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) := by grind
  clear eq86
  have eq94 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq98 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq60 eq92
    | exact resolve eq92 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq92
  have eq103 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq106 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq106
    | (have j0 := eq106 (σ X0) (σ X1)
       grind)
    | exact resolve eq106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq106 x y
       grind)
    | exact superpose eq106 eq44
    | (have j1 := eq106 x y
       grind)
    | exact resolve eq44 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq125 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq123
    | exact resolve eq123 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq126 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq125
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq125
    | exact resolve eq125 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq106
    | (have j0 := eq106 (σ x) (σ y)
       grind)
    | exact resolve eq106 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq129
    | exact resolve eq129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq133 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq130
       have r₂ := eq27
       grind)
    | exact resolve eq130 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq135 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq133
    | exact resolve eq133 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq139 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq135 eq55
    | exact resolve eq55 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq140 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq135 eq27
    | exact resolve eq27 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq146 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq151 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq139 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq139
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq139
       grind)
    | exact resolve eq12 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq139 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq139 eq14
    | exact resolve eq14 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq151
  have eq157 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq152
    | exact resolve eq152 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq158 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq155
    | exact resolve eq155 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq174 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (M.op X0 X0) (σ x))) ∨ (M.op (M.op X0 X0) (σ x)) = (k (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq154 eq12
    | (have j0 := eq12 (M.op (M.op X0 X0) (σ x)) (σ y)
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X0) (σ x)) (σ y)
       have r₂ := eq154 X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq154 X0
       grind)
    | exact resolve eq12 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq178 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (k (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (M.op X0 X0) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq174 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq384 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq178 sF2
       have i₂ := eq53 sF2 sF2
       grind)
    | exact superpose eq53 eq178
    | exact resolve eq178 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq389 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq384 eq139
    | exact resolve eq139 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq384
  have eq395 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq389
  have eq402 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq395 eq126
    | exact resolve eq126 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq395 eq81
    | exact resolve eq81 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq395
  have eq405 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq402
  have eq408 : x = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28 eq403
    | exact resolve eq403 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq403
  have eq417 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq405 eq126
    | exact resolve eq126 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq421 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq405 eq157
    | (have r₁ := eq157
       have r₂ := eq405
       grind)
    | exact resolve eq157 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq405
  have eq457 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq421
  have eq458 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq457
  have eq462 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq417
  have eq584 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq106 x y
       have i₂ := eq408
       grind)
    | exact superpose eq408 eq106
    | (have j0 := eq106 x y
       grind)
    | exact resolve eq106 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq585 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq584
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq584
    | exact resolve eq584 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq588 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq585
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq585
    | exact resolve eq585 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq589 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq588
  have eq600 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq589 eq140
    | exact resolve eq140 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq589
  have eq643 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq600
  have eq796 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq893 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq462 eq458
    | exact resolve eq458 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458 eq462
  have eq896 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq893
  have eq899 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq896
       have r₂ := eq27
       grind)
    | exact resolve eq896 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq916 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq899 eq158
    | exact resolve eq158 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq934 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq899 eq643
    | (have r₁ := eq643
       have r₂ := eq899
       grind)
    | exact resolve eq643 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq899
  have eq935 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq934
  have eq936 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq935
  have eq954 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq916
  have eq960 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq954
       have r₂ := eq27
       grind)
    | exact resolve eq954 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq1016 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq936 eq20
    | exact resolve eq20 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1017 : (σ (k x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq936 eq45
    | exact resolve eq45 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq1019 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq936 eq54
    | exact resolve eq54 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1024 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq936
  have eq1028 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1017
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1017
    | exact resolve eq1017 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1029 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1016
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1016
    | exact resolve eq1016 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq1049 : ∀ X0 : G, x ≠ (M.op (M.op X0 X0) (M.op x y)) ∨ (M.op x (M.op (M.op X0 X0) (M.op x y))) = (k x (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq64 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq64
    | (have j0 := eq64 x X0 y
       grind)
    | exact resolve eq64 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq1068 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1029 eq26
    | exact resolve eq26 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1070 : ∀ X0 : G, (σ (k y X0)) = (k (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1029 eq36
    | exact resolve eq36 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1071 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1029 eq40
    | exact resolve eq40 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1107 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41 eq1071
    | exact resolve eq1071 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1071
  have eq1108 : ∀ X0 : G, (σ (k y X0)) = (σ (k (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37 eq1070
    | exact resolve eq1070 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1070
  have eq1247 : x ≠ x ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1019
       grind)
    | exact superpose eq1019 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1019
       grind)
    | exact resolve eq12 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1254 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq1247
  have eq1256 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1254
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1254
    | exact resolve eq1254 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq1257 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq1256
  have eq1322 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq146
       have i₂ := eq1257
       grind)
    | exact superpose eq1257 eq146
    | exact resolve eq146 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1324 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1322
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1322
    | exact resolve eq1322 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1435 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1028 eq106
    | (have j0 := eq106 (σ x) (σ y)
       grind)
    | exact resolve eq106 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq1028
  have eq1437 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1435
    | exact resolve eq1435 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435
  have eq1440 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1437
    | exact resolve eq1437 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437
  have eq1717 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1068 eq59
    | (have j0 := eq59 (σ x) X0 (σ y)
       grind)
    | exact resolve eq59 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq1068
  have eq1836 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1440 eq103
    | exact resolve eq103 eq1440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq3030 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (σ (k X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1107 eq16
    | exact resolve eq16 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3051 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3030 X0
       have i₂ := eq16 (k X0 y)
       grind)
    | exact superpose eq16 eq3030
    | exact resolve eq3030 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3030
  have eq3184 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98 eq1108
    | exact resolve eq1108 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq1108
  have eq3227 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq3184
  have eq3254 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3227
       have i₂ := eq146
       grind)
    | exact superpose eq146 eq3227
    | exact resolve eq3227 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3227
  have eq3260 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3254
    | exact resolve eq3254 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3254
  have eq4450 : (σ (k x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1836 eq1107
    | exact resolve eq1107 eq1836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107 eq1836
  have eq4454 : (σ (k x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4450
  have eq4460 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4454
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq4454
    | exact resolve eq4454 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4454
  have eq4464 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4460
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq4460
    | exact resolve eq4460 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq4460
  have eq4707 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1029 eq4464
    | exact resolve eq4464 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4464
  have eq4733 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq4707
  have eq4735 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4733
       have r₂ := eq27
       grind)
    | exact resolve eq4733 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4733
  have eq4745 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4735 eq103
    | exact resolve eq103 eq4735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq4735
  have eq4760 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4745 eq3051
    | exact resolve eq3051 eq4745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3051 eq4745
  have eq4767 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq4760
  have eq4883 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq94
    | (have j0 := eq94 X0 X1
       grind)
    | exact resolve eq94 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq94
  have eq4915 : x = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4883 y x
       have i₂ := eq1019
       grind)
    | exact superpose eq1019 eq4883
    | (have j0 := eq4883 x y
       grind)
    | exact resolve eq4883 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019 eq4883
  have eq4961 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4915
       have r₂ := eq1024
       grind)
    | exact resolve eq4915 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024 eq4915
  have eq4976 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4767
       have i₂ := eq4961
       grind)
    | exact superpose eq4961 eq4767
    | exact resolve eq4767 eq4961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4767 eq4961
  have eq4982 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq4976
  have eq4999 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4982 eq15
    | exact resolve eq15 eq4982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4982
  have eq5014 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4999
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4999
    | exact resolve eq4999 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4999
  have eq5075 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5014 eq27
    | exact resolve eq27 eq5014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5079 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5014 eq68
    | (have r₁ := eq68
       have r₂ := eq5014
       grind)
    | exact resolve eq68 eq5014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq5093 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq5079
  have eq5550 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5093 eq1324
    | exact resolve eq1324 eq5093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq5552 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5093 eq3260
    | exact resolve eq3260 eq5093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3260 eq5093
  have eq5557 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq5552
  have eq5558 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq5550
  have eq5568 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1029 eq5557
    | exact resolve eq5557 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq5591 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq5568
  have eq5610 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5558 eq53
    | exact resolve eq53 eq5558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq5558
  have eq5765 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5610 eq1717
    | exact resolve eq1717 eq5610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717 eq5610
  have eq5777 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq5765
  have eq7579 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5557 eq5777
    | exact resolve eq5777 eq5557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5557 eq5777
  have eq7601 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq7579
  have eq7608 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5014 eq7601
    | exact resolve eq7601 eq5014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5014 eq7601
  have eq7626 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq7608
  have eq7703 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7626 eq5591
    | exact resolve eq5591 eq7626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5591 eq7626
  have eq7719 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq7703
  have eq7723 : x = (M.op x y) := by
    first
    | (have r₁ := eq7719
       have r₂ := eq5075
       grind)
    | exact resolve eq7719 eq5075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5075 eq7719
  have eq8065 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq7723 eq20
    | exact resolve eq20 eq7723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq8068 : x = (M.op x x) := by
    first
    | exact superpose eq7723 eq54
    | exact resolve eq54 eq7723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq8070 : x ≠ x ∨ (k y x) = (M.op y x) := by
    first
    | exact superpose eq7723 eq66
    | (have r₁ := eq66
       have r₂ := eq7723
       grind)
    | exact resolve eq66 eq7723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq8090 : (k y x) = (M.op y x) := by grind
  clear eq8070
  have eq8101 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq8065
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8065
    | exact resolve eq8065 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8065
  have eq8102 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq8101 eq26
    | exact resolve eq26 eq8101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq8521 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x X1
       have i₂ := eq8068
       grind)
    | exact superpose eq8068 eq14
    | exact resolve eq14 eq8068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8708 : ∀ X0 : G, x ≠ (M.op (M.op X0 X0) x) ∨ (M.op x (M.op (M.op X0 X0) (M.op x y))) = (k x (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq7723 eq1049
    | (have j0 := eq1049 X0
       grind)
    | exact resolve eq1049 eq7723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq8709 : ∀ X0 : G, x ≠ (M.op (M.op X0 X0) x) ∨ (M.op x (M.op (M.op X0 X0) x)) = (k x (M.op (M.op X0 X0) x)) := by
    intro X0
    first
    | exact superpose eq7723 eq8708
    | (have j0 := eq8708 X0
       grind)
    | exact resolve eq8708 eq7723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8708
  have eq8768 : x ≠ x ∨ (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq8709 (M.op x x)
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq8709
    | (have r₁ := eq8709 (M.op x x)
       have r₂ := eq14 x x x
       grind)
    | exact resolve eq8709 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8709
  have eq8769 : (k x x) = (M.op x x) := by grind
  clear eq8768
  have eq8771 : x = (k x x) := by
    first
    | (have i₁ := eq8769
       have i₂ := eq8068
       grind)
    | exact superpose eq8068 eq8769
    | exact resolve eq8769 eq8068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8068 eq8769
  have eq8783 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq796 x x
       have i₂ := eq8771
       grind)
    | exact superpose eq8771 eq796
    | (have j0 := eq796 x x
       grind)
    | exact resolve eq796 eq8771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq8771
  have eq8786 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8783
  have eq8789 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8786
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8786
    | exact resolve eq8786 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8786
  have eq8796 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq8101 eq8789
    | exact resolve eq8789 eq8101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8789
  have eq9099 : (k (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq146
       have i₂ := eq8090
       grind)
    | exact superpose eq8090 eq146
    | exact resolve eq146 eq8090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq8090
  have eq9108 : (k (σ y) (σ (M.op x y))) = (σ (M.op y x)) := by
    first
    | exact superpose eq8101 eq9099
    | exact resolve eq9099 eq8101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9099
  have eq11227 : (M.op y x) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq16 (M.op y x)
       have i₂ := eq9108
       grind)
    | exact superpose eq9108 eq16
    | exact resolve eq16 eq9108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9108
  have eq11281 : (τ (σ y)) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq960 eq11227
    | exact resolve eq11227 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq11227
  have eq11309 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq11281
    | exact resolve eq11281 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11281
  have eq11310 : y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq7723 eq11309
    | exact resolve eq11309 eq7723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11309
  have eq15113 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq8521 y x
       have i₂ := eq11310
       grind)
    | exact superpose eq11310 eq8521
    | exact resolve eq8521 eq11310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8521 eq11310
  have eq15206 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq15113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15113
    | exact resolve eq15113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15113
  have eq15241 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7723 eq15206
    | exact resolve eq15206 eq7723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15206
  have eq15256 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq15241
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15241
    | exact resolve eq15241 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq15241
  have eq15259 : x = y ∨ x = y := by
    first
    | exact superpose eq7723 eq15256
    | exact resolve eq15256 eq7723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7723 eq15256
  have eq15260 : x = y := by grind
  clear eq15259
  have eq15262 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq15260
       grind)
    | exact superpose eq15260 eq24
    | exact resolve eq24 eq15260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15260
  have eq15303 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15262
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15262
    | exact resolve eq15262 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15262
  have eq15315 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8101 eq15303
    | exact resolve eq15303 eq8101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8101 eq15303
  have eq15465 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15315 eq8102
    | exact resolve eq8102 eq15315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8102 eq15315
  have eq15484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8796 eq15465
    | exact resolve eq15465 eq8796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8796 eq15465
  have eq15518 : False := by grind
  exact eq15518

/-- `Equation2744`: `x = ((y ◇ y) ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation2744 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2744 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2744.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq511 : ∀ X0 X1 : G, (M.op (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq3688 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq511 X1 X0
       grind)
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq511 X0 X1
       grind)
    | exact superpose eq511 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq511 X1 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq511 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq511 X0 X1
       grind)
    | exact resolve eq13 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq3703 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3688 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3688
  have eq3704 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3703 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3703
  have eq4474 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3704 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3704
    | exact resolve eq3704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704
  have eq4573 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4474 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq4474
    | (have j0 := eq4474 X0 X1
       grind)
    | exact resolve eq4474 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq4474
  have eq4613 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq4573 X1 X0
       grind)
    | exact superpose eq4573 eq11
    | (have j1 := eq4573 X1 X0
       grind)
    | exact resolve eq11 eq4573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4573
  have eq4736 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4613 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4613
    | (have j0 := eq4613 X0 X1
       grind)
    | exact resolve eq4613 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4613
  have eq4861 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4736 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4736
  have eq4871 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4861 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq4861 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq4861 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq4861 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X1)
       grind)
    | exact resolve eq4861 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4861
  have eq4912 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq4871 X1 (τ X0)
       grind)
    | exact superpose eq4871 eq19
    | (have j1 := eq4871 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq4871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4934 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4871 (σ X1) (σ X0)
       grind)
    | exact superpose eq4871 eq15
    | (have j1 := eq4871 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq4871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4871
  have eq5276 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4912 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4912
    | exact resolve eq4912 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4912
  have eq5345 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5276 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5276
    | (have j0 := eq5276 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq5276 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5276
  have eq5749 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4934 x y
       grind)
    | exact superpose eq4934 eq16
    | (have j1 := eq4934 x y
       grind)
    | exact resolve eq16 eq4934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4934
  have eq5794 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5749
       have i₂ := eq5345 x y
       grind)
    | exact superpose eq5345 eq5749
    | (have j1 := eq5345 (σ x) (σ y)
       grind)
    | (have r₁ := eq5749
       have r₂ := eq5345 x y
       grind)
    | (have r₁ := eq5749
       have r₂ := eq5345 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5749
       have r₂ := eq5345 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5749 eq5345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5345 eq5749
  have eq5797 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5794
  have eq5800 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5797
       grind)
    | exact superpose eq5797 eq16
    | exact resolve eq16 eq5797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5797
  have eq5801 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5800
       have r₂ := eq22 x
       grind)
    | exact resolve eq5800 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5800
  have eq5802 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5801
       grind)
    | exact superpose eq5801 eq16
    | exact resolve eq16 eq5801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5803 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5801
       grind)
    | exact superpose eq5801 eq10
    | exact resolve eq10 eq5801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5801
  have eq5857 : x = y := by
    first
    | (have i₁ := eq5803
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5803
    | exact resolve eq5803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5803
  have eq5858 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5802
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5802
    | exact resolve eq5802 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5802
  have eq5859 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5858
       have i₂ := eq5857
       grind)
    | exact superpose eq5857 eq5858
    | exact resolve eq5858 eq5857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5857 eq5858
  have eq5860 : False := by grind
  exact eq5860

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_x_pxy_pyx_Equation2755 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
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
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq63 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq63
    | (have j0 := eq63 x y
       grind)
    | exact resolve eq63 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq63
    | (have j0 := eq63 (σ x) (σ y)
       grind)
    | exact resolve eq63 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (M.op X1 X0) X1
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (M.op X1 X1) (M.op (M.op X1 X1) X0)
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq63
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq64 eq63
    | exact resolve eq63 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X1
    grind
  clear eq63
  have eq90 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq67 (M.op X0 X0) X1
       grind)
    | exact superpose eq67 eq14
    | exact resolve eq14 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq68 (M.op X0 (M.op X1 X1)) X1
       have i₂ := eq67 (M.op X1 X1) X0
       grind)
    | exact superpose eq67 eq68
    | exact resolve eq68 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq95 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq68 (M.op X0 X0) X0
       grind)
    | exact superpose eq68 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq68 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq109 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X1
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq76 X0
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq76
    | exact resolve eq76 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq111 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq90 X1 X0
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq90 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq90 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq202 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq169
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq169
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq210 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq202
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq202
    | exact resolve eq202 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq211 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq210
    | exact resolve eq210 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq314 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (M.op X1 X1)
       have i₂ := eq100 X1 (τ X0)
       grind)
    | exact superpose eq100 eq35
    | exact resolve eq35 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq324 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq314 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq314
    | exact resolve eq314 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq377 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq538 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq377 X0 (M.op X1 X1)
       have i₂ := eq100 X1 (σ X0)
       grind)
    | exact superpose eq100 eq377
    | exact resolve eq377 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq377
  have eq558 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq538
    | exact resolve eq538 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq4076 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq324 (M.op X1 X1) X0
       have i₂ := eq109 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq109 eq324
    | (have j1 := eq109 X1 (σ (M.op X0 X0))
       grind)
    | exact resolve eq324 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq4101 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4076 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4076
  have eq4243 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq68 X2 x
       have i₂ := eq4101 X0 x
       grind)
    | exact superpose eq4101 eq68
    | exact resolve eq68 eq4101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4247 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq92 X1 x
       have i₂ := eq4101 X0 x
       grind)
    | exact superpose eq4101 eq92
    | exact resolve eq92 eq4101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4101
  have eq18504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq211 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq18505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq18504
    | exact resolve eq18504 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18504
  have eq18510 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq18505
       have r₂ := eq28
       grind)
    | exact resolve eq18505 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18505
  have eq18527 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq18510 eq558
    | exact resolve eq558 eq18510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18510
  have eq18591 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30 eq18527
    | exact resolve eq18527 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18527
  have eq18593 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq18591 X0
       have j1 := eq111 X0 y X0
       grind)
    | (have r₁ := eq18591 (M.op X0 X0)
       have r₂ := eq111 X0 (k (M.op X0 X0) y) x
       grind)
    | (have r₁ := eq18591 X0
       have r₂ := eq111 (σ x) (σ x) x
       grind)
    | (have r₁ := eq18591 X0
       have r₂ := eq111 x y x
       grind)
    | exact resolve eq18591 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18591
  have eq18609 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ (k X1 y) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 X1
       have i₂ := eq18593 (M.op X1 X1)
       grind)
    | exact superpose eq18593 eq558
    | (have j1 := eq18593 X1
       grind)
    | exact resolve eq558 eq18593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq18593
  have eq18672 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ (k X1 y) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq29 eq18609
    | (have j0 := eq18609 X0 X1
       grind)
    | exact resolve eq18609 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18609
  have eq18673 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq18672 X0 X1
       have j1 := eq111 X0 y X1
       grind)
    | (have r₁ := eq18672 (M.op X0 X0) X1
       have r₂ := eq111 X0 (k (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq18672 X0 (M.op X0 X0)
       have r₂ := eq111 X0 (k (M.op X0 X0) y) x
       grind)
    | (have r₁ := eq18672 X0 X1
       have r₂ := eq111 x x x
       grind)
    | exact resolve eq18672 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq18672
  have eq18734 : ∀ X0 X1 : G, y = (M.op X0 X0) ∨ y = (M.op X0 X0) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 y
       have i₂ := eq18673 X1 (M.op X0 X0)
       grind)
    | exact superpose eq18673 eq109
    | (have j0 := eq109 X0 y
       have j1 := eq18673 X1 X1
       grind)
    | exact resolve eq109 eq18673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18673
  have eq18753 : ∀ X0 X1 : G, y = (M.op X0 X0) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq18734 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18734
  have eq18885 : ∀ X1 X2 : G, (k X2 x) = X2 ∨ (M.op y X1) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq68 X1 x
       have i₂ := eq18753 x X2
       grind)
    | exact superpose eq18753 eq68
    | (have j1 := eq18753 x X2
       grind)
    | exact resolve eq68 eq18753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18753
  have eq19720 : ∀ X0 X1 : G, x = (M.op X0 X0) ∨ x = (M.op X0 X0) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 x
       have i₂ := eq18885 X1 (M.op X0 X0)
       grind)
    | exact superpose eq18885 eq109
    | (have j0 := eq109 X0 x
       have j1 := eq18885 X1 x
       grind)
    | exact resolve eq109 eq18885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq18885
  have eq19740 : ∀ X0 X1 : G, x = (M.op X0 X0) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq19720 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19720
  have eq22293 : ∀ X1 X2 : G, (M.op y X2) = X2 ∨ (M.op x X1) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq68 X1 x
       have i₂ := eq19740 x X2
       grind)
    | exact superpose eq19740 eq68
    | (have j1 := eq19740 x X2
       grind)
    | exact resolve eq68 eq19740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq19740
  have eq29021 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq72 eq22293
    | (have j0 := eq22293 X0 x
       grind)
    | exact resolve eq22293 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq22293
  have eq29134 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29021 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29021
    | (have j0 := eq29021 y
       grind)
    | exact resolve eq29021 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq29184 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4247 x X0
       have i₂ := eq29021 x
       grind)
    | exact superpose eq29021 eq4247
    | exact resolve eq4247 eq29021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4247 eq29021
  have eq29228 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29184 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29184
    | (have j0 := eq29184 X0
       grind)
    | exact resolve eq29184 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29184
  have eq29240 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29134 eq21
    | exact resolve eq21 eq29134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29134
  have eq29374 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29240
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq29240
    | exact resolve eq29240 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29240
  have eq32068 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq65 eq29228
    | exact resolve eq29228 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq29228
  have eq32192 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32068 eq28
    | exact resolve eq28 eq32068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32068
  have eq32193 : x = (M.op x y) := by
    first
    | (have r₁ := eq32192
       have r₂ := eq29374
       grind)
    | exact resolve eq32192 eq29374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29374 eq32192
  have eq32195 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq32193 eq21
    | exact resolve eq21 eq32193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq32198 : y = (M.op x x) := by
    first
    | exact superpose eq32193 eq64
    | exact resolve eq64 eq32193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq32193
  have eq32341 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq32195
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32195
    | exact resolve eq32195 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq32195
  have eq32345 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq32341 eq27
    | exact resolve eq27 eq32341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32341
  have eq32424 : ∀ X0 : G, y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq32198
       have i₂ := eq90 X0 x
       grind)
    | (have i₁ := eq32198
       have i₂ := eq90 x X0
       grind)
    | exact superpose eq90 eq32198
    | exact resolve eq32198 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq32445 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq92 X0 x
       have i₂ := eq32198
       grind)
    | exact superpose eq32198 eq92
    | exact resolve eq92 eq32198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq32198
  have eq32724 : ∀ X0 : G, y = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4243 X0 (σ (M.op X0 X0))
       have i₂ := eq32424 (σ (M.op X0 X0))
       grind)
    | exact superpose eq32424 eq4243
    | exact resolve eq4243 eq32424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4243
  have eq32767 : y = (σ y) := by
    first
    | (have i₁ := eq32724 x
       have i₂ := eq32424 x
       grind)
    | exact superpose eq32424 eq32724
    | exact resolve eq32724 eq32424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32424 eq32724
  have eq32853 : y = (σ y) := by
    first
    | (have i₁ := eq32767
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32767
    | exact resolve eq32767 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq32767
  have eq32932 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) y) := by
    first
    | exact superpose eq32853 eq32345
    | exact resolve eq32345 eq32853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32345 eq32853
  have eq38898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32932
       have i₂ := eq32445 sF1
       grind)
    | exact superpose eq32445 eq32932
    | exact resolve eq32932 eq32445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32445 eq32932
  have eq38899 : False := by grind
  exact eq38899

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_y_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X2 X2) (M.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 (M.op (M.op X2 X2) (M.op X3 X0))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (M.op X0 (M.op X2 X2)) X1 (M.op X2 X2) (M.op X3 X3)
       have i₂ := eq24 (M.op X2 X2) X2 X3 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq119 : ∀ X2 X3 : G, (M.op X2 X2) = (M.op X3 X3) := by
    intro X2 X3
    first
    | (have i₁ := eq107 x x X3 X2
       have i₂ := eq9 (M.op X3 X3) x x
       grind)
    | exact superpose eq9 eq107
    | exact resolve eq107 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq138 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq119 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq119 x x
       grind)
    | exact resolve eq13 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq138 (σ X0) (σ X1)
       grind)
    | exact superpose eq138 eq15
    | (have j1 := eq138 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 X1
       have i₂ := eq138 X0 X1
       grind)
    | exact superpose eq138 eq150
    | (have j0 := eq150 X0 X1
       have j1 := eq138 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq150 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq150
  have eq660 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq119 (σ X1) X0
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq119 X0 (σ X1)
       grind)
    | exact superpose eq119 eq22
    | exact resolve eq22 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq119
  have eq1977 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq152 x y
       grind)
    | exact superpose eq152 eq16
    | (have j1 := eq152 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq152 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq152 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq152 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq1991 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1977
  have eq3003 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1991
       grind)
    | exact superpose eq1991 eq10
    | exact resolve eq10 eq1991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991
  have eq3026 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3003
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3003
    | exact resolve eq3003 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq3027 : x = y := by grind
  clear eq3026
  have eq5686 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3027
       grind)
    | exact superpose eq3027 eq16
    | exact resolve eq16 eq3027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3027
  have eq5687 : False := by grind
  exact eq5687

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyx_pxy_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq43 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (M.op X1 X0) X1
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq43
    | exact resolve eq43 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X2 X0)
       have i₂ := eq43 X2 X0
       grind)
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq45 (M.op X0 X0) X1
       grind)
    | exact superpose eq45 eq9
    | exact resolve eq9 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq99
    | (have j0 := eq99 X0 X1
       grind)
    | exact resolve eq99 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq136 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq54
    | exact resolve eq54 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq140 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq45 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq45
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq329 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101 x y
       grind)
    | exact superpose eq101 eq16
    | (have j1 := eq101 x y
       grind)
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq6174 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq329
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq329
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq329
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq329
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq329 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq6175 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq6174
  have eq62016 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6175
       grind)
    | exact superpose eq6175 eq16
    | exact resolve eq16 eq6175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6175
  have eq62017 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq62016
       have r₂ := eq136 x (σ x)
       grind)
    | exact resolve eq62016 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62016
  have eq1034725 : (σ x) = (M.op (σ y) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45 (σ y) (σ x)
       have i₂ := eq62017
       grind)
    | exact superpose eq62017 eq45
    | exact resolve eq45 eq62017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq62017
  have eq1034749 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1034725
       have i₂ := eq140 y
       grind)
    | exact superpose eq140 eq1034725
    | exact resolve eq1034725 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq1034725
  have eq1034750 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq1034749
  have eq1034766 : y = (τ (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1034750
       grind)
    | exact superpose eq1034750 eq10
    | exact resolve eq10 eq1034750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034750
  have eq1035029 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1034766
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1034766
    | exact resolve eq1034766 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034766
  have eq1035031 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1035029
       grind)
    | exact superpose eq1035029 eq16
    | exact resolve eq16 eq1035029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035029
  have eq1035032 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq1035031
       have r₂ := eq136 x (σ x)
       grind)
    | exact resolve eq1035031 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035031
  have eq1036560 : ∀ X0 : G, y = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq49 y X0 y
       have i₂ := eq1035032
       grind)
    | exact superpose eq1035032 eq49
    | exact resolve eq49 eq1035032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035032
  have eq1036570 : x = y := by
    first
    | (have i₁ := eq1036560 x
       have i₂ := eq49 y x x
       grind)
    | exact superpose eq49 eq1036560
    | exact resolve eq1036560 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1036560
  have eq1036577 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1036570
       grind)
    | exact superpose eq1036570 eq16
    | exact resolve eq16 eq1036570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036570
  have eq1036578 : False := by grind
  exact eq1036578
