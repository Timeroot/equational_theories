import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pyx_pyy_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq54 X0
       have r₂ := eq12 X0 X0
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
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq233 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq257 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq233 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq233
    | (have j0 := eq233 X0 X1
       grind)
    | exact resolve eq233 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq233
  have eq262 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq257 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq257 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq257 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq257 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq265 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq262 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq262
    | (have j0 := eq262 X0 X1
       grind)
    | exact resolve eq262 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq262
  have eq453 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq265 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq265
    | exact resolve eq265 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq265 (σ X0) X1
       grind)
    | exact superpose eq265 eq15
    | (have j1 := eq265 (σ X0) X1
       grind)
    | exact resolve eq15 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq483 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq460 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq460
    | (have j0 := eq460 X0 X1
       grind)
    | exact resolve eq460 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq511 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq453 (τ X1) X0
       grind)
    | exact superpose eq453 eq17
    | (have j1 := eq453 (τ X1) X0
       grind)
    | exact resolve eq17 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq453
  have eq820 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq511 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq511
    | exact resolve eq511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq860 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq820 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq820
    | (have j0 := eq820 X0 X1
       grind)
    | exact resolve eq820 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq3631 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq483 x y
       grind)
    | exact superpose eq483 eq16
    | (have j1 := eq483 x y
       grind)
    | exact resolve eq16 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3655 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq483 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq3689 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3631
       have i₂ := eq860 y x
       grind)
    | exact superpose eq860 eq3631
    | (have j1 := eq860 y x
       grind)
    | (have r₁ := eq3631
       have r₂ := eq860 y x
       grind)
    | exact resolve eq3631 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631
  have eq3690 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3689
  have eq3716 : y ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3690
       grind)
    | exact superpose eq3690 eq12
    | exact resolve eq12 eq3690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3717 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3690
       grind)
    | exact superpose eq3690 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3690
       grind)
    | exact resolve eq13 eq3690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3690
  have eq3725 : (k y x) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3717
  have eq3726 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq3716
       have r₂ := eq3725
       grind)
    | exact resolve eq3716 eq3725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3716 eq3725
  have eq3734 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq249 x y
       have i₂ := eq3726
       grind)
    | exact superpose eq3726 eq249
    | (have j0 := eq249 x y
       grind)
    | exact resolve eq249 eq3726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq3746 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3734
  have eq3747 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3746
  have eq3880 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3747
       grind)
    | exact superpose eq3747 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3747
       grind)
    | exact resolve eq12 eq3747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3747
  have eq3889 : (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3880
  have eq3897 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq3889
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3889
    | exact resolve eq3889 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3889
  have eq4136 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3897
       grind)
    | exact superpose eq3897 eq12
    | exact resolve eq12 eq3897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4137 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3897
       grind)
    | exact superpose eq3897 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq3897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3897
  have eq4145 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq4137
       have r₂ := eq66 x
       grind)
    | exact resolve eq4137 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4137
  have eq4146 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq4136
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4136
    | exact resolve eq4136 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136
  have eq4147 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq4145
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4145
    | exact resolve eq4145 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4145
  have eq4148 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq4147
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq4147
    | exact resolve eq4147 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147
  have eq4149 : (σ y) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4148
       have r₂ := eq4146
       grind)
    | exact resolve eq4148 eq4146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4146 eq4148
  have eq4284 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq4149
  have eq4483 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3655 x y
       have i₂ := eq3726
       grind)
    | exact superpose eq3726 eq3655
    | (have j0 := eq3655 x y
       grind)
    | exact resolve eq3655 eq3726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3655 eq3726
  have eq4509 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4483
  have eq4510 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4509
  have eq4592 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4510
       grind)
    | exact superpose eq4510 eq16
    | exact resolve eq16 eq4510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4596 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq4510
       grind)
    | exact superpose eq4510 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq4510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4510
  have eq4604 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4596
       have r₂ := eq66 x
       grind)
    | exact resolve eq4596 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4596
  have eq4606 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4604
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4604
    | exact resolve eq4604 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4604
  have eq4607 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4606
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq4606
    | exact resolve eq4606 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq4606
  have eq4608 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4607
       have r₂ := eq4284
       grind)
    | exact resolve eq4607 eq4284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4284 eq4607
  have eq4741 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq860 y x
       have i₂ := eq4608
       grind)
    | exact superpose eq4608 eq860
    | (have j0 := eq860 y x
       grind)
    | exact resolve eq860 eq4608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq4608
  have eq4802 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq4741
       have r₂ := eq4592
       grind)
    | exact resolve eq4741 eq4592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4741
  have eq4948 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4592
       have i₂ := eq4802
       grind)
    | exact superpose eq4802 eq4592
    | exact resolve eq4592 eq4802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4592 eq4802
  have eq4963 : False := by grind
  exact eq4963

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pxx_y_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
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
  have eq50 : y = (M.op y (M.op y (M.op y (M.op x y)))) := by
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
  have eq51 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq63 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq74 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) := by
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
  have eq75 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq584
    | exact resolve eq584 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq588 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq585
       have r₂ := eq27
       grind)
    | exact resolve eq585 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq590 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq588
    | exact resolve eq588 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq592 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq590
    | exact resolve eq590 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq594 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq592 eq63
    | (have r₁ := eq63
       have r₂ := eq592
       grind)
    | exact resolve eq63 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq592 eq51
    | exact resolve eq51 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq592 eq27
    | exact resolve eq27 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq598 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq594
  have eq650 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq93 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq654 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq650 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq650 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq650 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq650 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq664 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq654 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq654
    | (have j0 := eq654 X0 X1
       grind)
    | exact resolve eq654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq674 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq598 eq114
    | exact resolve eq114 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq677 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq674
  have eq714 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq595 eq14
    | exact resolve eq14 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq739 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq714 eq677
    | exact resolve eq677 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677 eq714
  have eq745 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq739
  have eq749 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq745
       have r₂ := eq596
       grind)
    | exact resolve eq745 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq745
  have eq753 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq749 eq75
    | (have r₁ := eq75
       have r₂ := eq749
       grind)
    | exact resolve eq75 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq756 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq749 eq27
    | exact resolve eq27 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq753
  have eq818 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq757 eq114
    | exact resolve eq114 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq822 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq818
  have eq829 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq822
       have r₂ := eq756
       grind)
    | exact resolve eq822 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq822
  have eq833 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq829 eq26
    | exact resolve eq26 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq829 eq114
    | exact resolve eq114 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq829
  have eq859 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq842
  have eq1035 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq833 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq833
       grind)
    | exact resolve eq13 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq1037 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1035
       have r₂ := eq749
       grind)
    | exact resolve eq1035 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq1035
  have eq1111 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1037 eq859
    | exact resolve eq859 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859 eq1037
  have eq1115 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1111
  have eq1118 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1115
       have r₂ := eq27
       grind)
    | exact resolve eq1115 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1120 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1118 eq20
    | exact resolve eq20 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1122 : y = (M.op y (M.op y (M.op y y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1118 eq50
    | exact resolve eq50 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1123 : y ≠ y ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1118 eq62
    | (have r₁ := eq62
       have r₂ := eq1118
       grind)
    | exact resolve eq62 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1118
  have eq1133 : (k y x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1123
  have eq1143 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1120
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1120
    | exact resolve eq1120 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1191 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1143 eq26
    | exact resolve eq26 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1235 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1191 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1191
       grind)
    | exact resolve eq12 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1238 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1235
       have r₂ := eq27
       grind)
    | exact resolve eq1235 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1295 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq1133
       grind)
    | exact superpose eq1133 eq71
    | exact resolve eq71 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq2452 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq1122
       grind)
    | exact superpose eq1122 eq14
    | exact resolve eq14 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq2462 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1295
       have i₂ := eq2452
       grind)
    | exact superpose eq2452 eq1295
    | exact resolve eq1295 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295 eq2452
  have eq2469 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2462
  have eq2471 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2469
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2469
    | exact resolve eq2469 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469
  have eq2478 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1143 eq2471
    | exact resolve eq2471 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2495 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2471 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq2471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2471
  have eq2496 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2495
  have eq2512 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2478
  have eq2513 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2496
    | exact resolve eq2496 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2496
  have eq2517 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2513
    | exact resolve eq2513 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513
  have eq4540 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2517 eq27
    | exact resolve eq27 eq2517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2517
  have eq4552 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4540
       have r₂ := eq1143
       grind)
    | exact resolve eq4540 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143 eq4540
  have eq4556 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4552 eq27
    | exact resolve eq27 eq4552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4562 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4552 eq1238
    | (have r₁ := eq1238
       have r₂ := eq4552
       grind)
    | exact resolve eq1238 eq4552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238 eq4552
  have eq4563 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4562
  have eq4564 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4563
  have eq4575 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4564 eq2512
    | exact resolve eq2512 eq4564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512 eq4564
  have eq4585 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq4575
  have eq4590 : x = (M.op x y) := by
    first
    | (have r₁ := eq4585
       have r₂ := eq4556
       grind)
    | exact resolve eq4585 eq4556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4556 eq4585
  have eq4594 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq4590 eq20
    | exact resolve eq20 eq4590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq4599 : x ≠ x ∨ x = y ∨ x = (k y x) := by
    first
    | exact superpose eq4590 eq74
    | (have r₁ := eq74
       have r₂ := eq4590
       grind)
    | exact resolve eq74 eq4590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq4613 : x = (k y x) ∨ x = y := by grind
  clear eq4599
  have eq4627 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4594
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4594
    | exact resolve eq4594 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4594
  have eq4637 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq4627 eq26
    | exact resolve eq26 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5271 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq71
       have i₂ := eq4613
       grind)
    | exact superpose eq4613 eq71
    | exact resolve eq71 eq4613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq5279 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq652 x y
       have i₂ := eq4613
       grind)
    | exact superpose eq4613 eq652
    | (have j0 := eq652 x y
       grind)
    | exact resolve eq652 eq4613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq4613
  have eq5282 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq5279
  have eq5291 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq5282
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5282
    | exact resolve eq5282 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5282
  have eq5295 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq4627 eq5271
    | exact resolve eq5271 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5271
  have eq5297 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq5291
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5291
    | exact resolve eq5291 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5291
  have eq5301 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq5295
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5295
    | exact resolve eq5295 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5295
  have eq5302 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq5297
    | exact resolve eq5297 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5297
  have eq5306 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq4627 eq5301
    | exact resolve eq5301 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5301
  have eq5307 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4627 eq5302
    | exact resolve eq5302 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5302
  have eq5311 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq5307
       have r₂ := eq27
       grind)
    | exact resolve eq5307 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5307
  have eq5315 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq5311
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5311
    | exact resolve eq5311 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5311
  have eq5319 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq5315
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5315
    | exact resolve eq5315 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5315
  have eq5323 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq5319
    | exact resolve eq5319 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5319
  have eq5338 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq5323 eq27
    | exact resolve eq27 eq5323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5339 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ x = y := by
    first
    | exact superpose eq5323 eq51
    | exact resolve eq51 eq5323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq5340 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq5323 eq63
    | (have r₁ := eq63
       have r₂ := eq5323
       grind)
    | exact resolve eq63 eq5323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq5323
  have eq5347 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq5340
  have eq5348 : (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq4627 eq5347
    | exact resolve eq5347 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5347
  have eq6306 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq5348 eq5306
    | exact resolve eq5306 eq5348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5306 eq5348
  have eq6317 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq6306
  have eq8134 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq5339 eq14
    | exact resolve eq14 eq5339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5339
  have eq8155 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq8134 eq6317
    | exact resolve eq6317 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6317 eq8134
  have eq8165 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq8155
  have eq8170 : x = y := by
    first
    | (have r₁ := eq8165
       have r₂ := eq5338
       grind)
    | exact resolve eq8165 eq5338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5338 eq8165
  have eq8172 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8170
       grind)
    | exact superpose eq8170 eq18
    | exact resolve eq18 eq8170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq8173 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8170
       grind)
    | exact superpose eq8170 eq24
    | exact resolve eq24 eq8170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8170
  have eq8233 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq8173
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8173
    | exact resolve eq8173 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8173
  have eq8234 : x = (M.op x x) := by
    first
    | exact superpose eq4590 eq8172
    | exact resolve eq8172 eq4590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4590 eq8172
  have eq8249 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4627 eq8233
    | exact resolve eq8233 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8233
  have eq8359 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq8249 eq4637
    | exact resolve eq4637 eq8249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4637 eq8249
  have eq8389 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq8234
       grind)
    | exact superpose eq8234 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq8234
       grind)
    | exact resolve eq13 eq8234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8234
  have eq8396 : x = (k x x) := by grind
  clear eq8389
  have eq8441 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq664 x x
       have i₂ := eq8396
       grind)
    | exact superpose eq8396 eq664
    | (have j0 := eq664 x x
       grind)
    | exact resolve eq664 eq8396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq8396
  have eq8446 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8441
  have eq8447 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8446
  have eq8458 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8447
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8447
    | exact resolve eq8447 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8447
  have eq8466 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4627 eq8458
    | exact resolve eq8458 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4627 eq8458
  have eq8474 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8359 eq8466
    | exact resolve eq8466 eq8359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8359 eq8466
  have eq8482 : False := by grind
  exact eq8482

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq81 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq67
    | (have j0 := eq67 (σ X0) (σ X1)
       grind)
    | exact resolve eq67 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq536 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq81 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq81 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq542 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq536 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq547 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq542 X0 X1
       have j1 := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq542 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | exact resolve eq542 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq563 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq547 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq547
    | (have j0 := eq547 X0 X1
       grind)
    | exact resolve eq547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq564 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq563 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq857 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq564 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq564
    | (have j0 := eq564 x X0
       grind)
    | exact resolve eq564 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq864 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq564 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq564
    | exact resolve eq564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq902 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq864 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq864
    | exact resolve eq864 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq864
  have eq950 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq857 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq857
    | (have j0 := eq857 y
       grind)
    | exact resolve eq857 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq857
  have eq960 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq950
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq950
    | exact resolve eq950 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq971 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq960
    | exact resolve eq960 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq960
  have eq2027 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq902 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq902
    | exact resolve eq902 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq2151 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq2027 x y
       grind)
    | exact superpose eq2027 eq73
    | exact resolve eq73 eq2027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq2027
  have eq2185 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq971 eq2151
    | exact resolve eq2151 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971 eq2151
  have eq2220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2185
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2185
    | exact resolve eq2185 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2185
  have eq2235 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2220
    | exact resolve eq2220 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2220
  have eq2249 : False := by grind
  exact eq2249

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq63 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X0 (M.op X0 (M.op X1 X0))) X0) = (k (M.op X0 (M.op X0 (M.op X1 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 (M.op X1 X0))) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 (M.op X0 (M.op X1 X0))) X0
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X0 (M.op X1 X0))) X0
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 (M.op X1 X0))) X0) = (k (M.op X0 (M.op X0 (M.op X1 X0))) X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq66 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq93 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
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
  have eq738 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq64 X0 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq64
    | (have j1 := eq66 X0
       grind)
    | exact resolve eq64 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq66
  have eq747 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq738 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq764 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq747 (σ X0)
       grind)
    | exact superpose eq747 eq15
    | exact resolve eq15 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq764 X0
       have i₂ := eq747 X0
       grind)
    | exact superpose eq747 eq764
    | exact resolve eq764 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq764
  have eq2003 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq2028 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2003 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2003
    | (have j0 := eq2003 X0 X1
       grind)
    | exact resolve eq2003 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2003
  have eq2042 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq2028 X1 X0
       grind)
    | exact superpose eq2028 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq2028 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq2028 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq2028 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq2028 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028
  have eq2052 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2042 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042
  have eq2073 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2052 X1 X0
       grind)
    | exact superpose eq2052 eq10
    | (have j1 := eq2052 X1 X0
       grind)
    | exact resolve eq10 eq2052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2121 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2073 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2073
    | (have j0 := eq2073 X0 X1
       grind)
    | exact resolve eq2073 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073
  have eq2122 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2121 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121
  have eq2150 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq2122 X0 (τ X1)
       grind)
    | exact superpose eq2122 eq19
    | (have j1 := eq2122 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2153 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2122 (σ X0) (σ X1)
       grind)
    | exact superpose eq2122 eq15
    | (have j1 := eq2122 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq2290 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2150 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2150
    | exact resolve eq2150 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150
  have eq2353 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2290 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2290
    | (have j0 := eq2290 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq2290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq2616 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2153 x y
       grind)
    | exact superpose eq2153 eq16
    | (have j1 := eq2153 x y
       grind)
    | exact resolve eq16 eq2153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153
  have eq2656 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2616
       have i₂ := eq2353 y x
       grind)
    | exact superpose eq2353 eq2616
    | (have j1 := eq2353 (σ x) (σ y)
       grind)
    | (have r₁ := eq2616
       have r₂ := eq2353 y x
       grind)
    | (have r₁ := eq2616
       have r₂ := eq2353 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2616
       have r₂ := eq2353 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2616 eq2353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353 eq2616
  have eq2659 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq2656
  have eq2662 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2659
       grind)
    | exact superpose eq2659 eq16
    | exact resolve eq16 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2659
  have eq2663 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq2662
       have r₂ := eq783 x
       grind)
    | exact resolve eq2662 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662
  have eq2728 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2663
       grind)
    | exact superpose eq2663 eq16
    | exact resolve eq16 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2729 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2663
       grind)
    | exact superpose eq2663 eq10
    | exact resolve eq10 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2663
  have eq2783 : x = y := by
    first
    | (have i₁ := eq2729
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2729
    | exact resolve eq2729 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2729
  have eq2784 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2728
       have i₂ := eq783 x
       grind)
    | exact superpose eq783 eq2728
    | exact resolve eq2728 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq2728
  have eq2790 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2784
       have i₂ := eq2783
       grind)
    | exact superpose eq2783 eq2784
    | exact resolve eq2784 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783 eq2784
  have eq2791 : False := by grind
  exact eq2791

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq133 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq82 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq82 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq142 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq143 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq145 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq143
    | (have j0 := eq143 X0 X1
       grind)
    | exact resolve eq143 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq148 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1
       have j1 := eq139 X1 X0
       grind)
    | (have r₁ := eq145 X1 X0
       have r₂ := eq139 X0 X1
       grind)
    | (have r₁ := eq145 X1 (k X0 X1)
       have r₂ := eq139 X0 X1
       grind)
    | (have r₁ := eq145 X1 X1
       have r₂ := eq139 X1 X1
       grind)
    | exact resolve eq145 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq145
  have eq539 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq148 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq148
    | exact resolve eq148 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq148 y x
       grind)
    | exact superpose eq148 eq16
    | (have j1 := eq148 y x
       grind)
    | exact resolve eq16 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq559 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq539 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq539
    | (have j0 := eq539 X0 X1
       grind)
    | exact resolve eq539 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq539
  have eq561 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq559
    | exact resolve eq559 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq622 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq561 (τ X0) X1
       grind)
    | exact superpose eq561 eq18
    | (have j1 := eq561 (τ X0) X1
       grind)
    | exact resolve eq18 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq561
  have eq785 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq622 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq622
    | exact resolve eq622 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq834 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq785 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq785
    | (have j0 := eq785 X0 X1
       grind)
    | exact resolve eq785 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq949 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq547
       have i₂ := eq834 x y
       grind)
    | exact superpose eq834 eq547
    | (have j1 := eq834 (σ x) (σ y)
       grind)
    | (have r₁ := eq547
       have r₂ := eq834 x y
       grind)
    | exact resolve eq547 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq950 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq949
  have eq995 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq950
  have eq1000 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq547
       have i₂ := eq995
       grind)
    | exact superpose eq995 eq547
    | exact resolve eq547 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq995
  have eq1001 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1000
  have eq1002 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1001
  have eq1054 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1002
  have eq1060 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1054
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1054
    | exact resolve eq1054 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1065 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1060
       grind)
    | exact superpose eq1060 eq16
    | exact resolve eq16 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1123 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1065
       have i₂ := eq834 x y
       grind)
    | exact superpose eq834 eq1065
    | (have j1 := eq834 x y
       grind)
    | (have r₁ := eq1065
       have r₂ := eq834 x y
       grind)
    | exact resolve eq1065 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq1124 : x = (M.op y y) := by grind
  clear eq1123
  have eq1129 : (M.op x y) = (k x y) := by grind
  clear eq1124
  have eq1204 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1065
       have i₂ := eq1129
       grind)
    | exact superpose eq1129 eq1065
    | exact resolve eq1065 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065 eq1129
  have eq1207 : False := by grind
  exact eq1207

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq194 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq83 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq198 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq194 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq199 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq201 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq199
    | (have j0 := eq199 X0 X1
       grind)
    | exact resolve eq199 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq205 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       have j1 := eq197 X0 X1
       grind)
    | (have r₁ := eq201 X0 X1
       have r₂ := eq197 X0 X1
       grind)
    | (have r₁ := eq201 X0 (k X1 X0)
       have r₂ := eq197 X0 X1
       grind)
    | (have r₁ := eq201 X0 X0
       have r₂ := eq197 X0 X0
       grind)
    | exact resolve eq201 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq201
  have eq514 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq205 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq205
    | exact resolve eq205 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  clear eq205
  have eq542 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq514 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq514
    | (have j0 := eq514 X0 X1
       grind)
    | exact resolve eq514 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq514
  have eq543 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq542 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq542
    | exact resolve eq542 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq602 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq543 (τ X1) X0
       grind)
    | exact superpose eq543 eq18
    | (have j1 := eq543 (τ X1) X0
       grind)
    | exact resolve eq18 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq543
  have eq840 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq602 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq602
    | exact resolve eq602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq893 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq840 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq840
    | (have j0 := eq840 X0 X1
       grind)
    | exact resolve eq840 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq955 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq528
       have i₂ := eq893 y x
       grind)
    | exact superpose eq893 eq528
    | (have j1 := eq893 (σ y) (σ x)
       grind)
    | (have r₁ := eq528
       have r₂ := eq893 y x
       grind)
    | exact resolve eq528 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq955
  have eq961 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq956
  have eq1007 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq528
       have i₂ := eq961
       grind)
    | exact superpose eq961 eq528
    | exact resolve eq528 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq961
  have eq1008 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1007
  have eq1009 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1008
  have eq1021 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1009
  have eq1027 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1021
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1021
    | exact resolve eq1021 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1062 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1027
       grind)
    | exact superpose eq1027 eq16
    | exact resolve eq16 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1070 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1062
       have i₂ := eq893 y x
       grind)
    | exact superpose eq893 eq1062
    | (have j1 := eq893 y x
       grind)
    | (have r₁ := eq1062
       have r₂ := eq893 y x
       grind)
    | exact resolve eq1062 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq1071 : y = (M.op x x) := by grind
  clear eq1070
  have eq1109 : (M.op x y) = (k y x) := by grind
  clear eq1071
  have eq1114 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1062
       have i₂ := eq1109
       grind)
    | exact superpose eq1109 eq1062
    | exact resolve eq1062 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq1109
  have eq1117 : False := by grind
  exact eq1117

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq266 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq267 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq267 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq280 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq269 (σ X0)
       grind)
    | exact superpose eq269 eq15
    | exact resolve eq15 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq280
    | exact resolve eq280 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq280
  have eq344 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq346 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq344 X0 X1
       have j1 := eq345 X0 X1
       grind)
    | (have r₁ := eq344 X0 X1
       have r₂ := eq345 X0 X1
       grind)
    | exact resolve eq344 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq345
  have eq364 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq346 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq346
    | exact resolve eq346 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq346 y (σ x)
       grind)
    | exact superpose eq346 eq16
    | (have j1 := eq346 y (σ x)
       grind)
    | exact resolve eq16 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq376 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq368
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq368
    | exact resolve eq368 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq383 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq364 X1 X0
       grind)
    | exact superpose eq364 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq364 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq364 X0 X1
       grind)
    | exact resolve eq13 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq383 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq390 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq388 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq388 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq388 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq405 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq390 X0 (τ X1)
       grind)
    | exact superpose eq390 eq18
    | (have j1 := eq390 X0 (τ X1)
       grind)
    | exact resolve eq18 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq422 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq390 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq405 (τ X0) X1
       grind)
    | exact superpose eq405 eq17
    | (have j1 := eq405 (τ X0) X1
       grind)
    | exact resolve eq17 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq405
  have eq1115 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1110 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1110
    | (have j0 := eq1110 X0 X1
       grind)
    | exact resolve eq1110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1129 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1115 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1115
    | (have j0 := eq1115 X0 X1
       grind)
    | exact resolve eq1115 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1132 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1129 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1129
    | (have j0 := eq1129 X0 X1
       grind)
    | exact resolve eq1129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1199 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1132 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1132
    | (have j0 := eq1132 X1 (σ X0)
       grind)
    | exact resolve eq1132 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1596 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1199 X0 X0
       have i₂ := eq390 X0 (σ X0)
       grind)
    | exact superpose eq390 eq1199
    | (have j0 := eq1199 X1 X0
       have j1 := eq390 X0 (σ X1)
       grind)
    | exact resolve eq1199 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq1199
  have eq1635 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1596 X0 X1
       have j1 := eq422 X0 (σ X1)
       grind)
    | (have r₁ := eq1596 X0 X1
       have r₂ := eq422 X0 (σ X1)
       grind)
    | exact resolve eq1596 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422 eq1596
  have eq1821 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1635 (σ X0) X1
       grind)
    | exact superpose eq1635 eq28
    | (have j1 := eq1635 (σ X0) X1
       grind)
    | exact resolve eq28 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1635
  have eq1832 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1821 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1821
    | (have j0 := eq1821 X0 X1
       grind)
    | exact resolve eq1821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821
  have eq1847 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1832 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1832
    | (have j0 := eq1832 X0 X1
       grind)
    | exact resolve eq1832 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832
  have eq1856 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1847 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1847
    | (have j0 := eq1847 X0 X1
       grind)
    | exact resolve eq1847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq1959 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1856 x y
       grind)
    | exact superpose eq1856 eq16
    | (have j1 := eq1856 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1856 x y
       grind)
    | exact resolve eq16 eq1856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856
  have eq1986 : x = (k x y) := by grind
  clear eq1959
  have eq2190 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq376
       have i₂ := eq364 y x
       grind)
    | exact superpose eq364 eq376
    | (have j1 := eq364 y x
       grind)
    | exact resolve eq376 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2191 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq2190
  have eq2193 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2191
       have i₂ := eq1986
       grind)
    | exact superpose eq1986 eq2191
    | exact resolve eq2191 eq1986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2191
  have eq2195 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2193
       have i₂ := eq1986
       grind)
    | exact superpose eq1986 eq2193
    | exact resolve eq2193 eq1986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2197 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq376
       have i₂ := eq2195
       grind)
    | exact superpose eq2195 eq376
    | exact resolve eq376 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq2195
  have eq2209 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2197
  have eq2210 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2209
       have i₂ := eq1986
       grind)
    | exact superpose eq1986 eq2209
    | exact resolve eq2209 eq1986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2209
  have eq2211 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2210
  have eq2213 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2211
       grind)
    | exact superpose eq2211 eq16
    | exact resolve eq16 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211
  have eq2272 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2213
       have i₂ := eq364 y x
       grind)
    | exact superpose eq364 eq2213
    | (have j1 := eq364 y x
       grind)
    | exact resolve eq2213 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq2273 : (M.op x y) = (k x y) := by grind
  clear eq2272
  have eq2276 : x = (M.op x y) := by
    first
    | (have i₁ := eq2273
       have i₂ := eq1986
       grind)
    | exact superpose eq1986 eq2273
    | exact resolve eq2273 eq1986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986 eq2273
  have eq2278 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2213
       have i₂ := eq2276
       grind)
    | exact superpose eq2276 eq2213
    | exact resolve eq2213 eq2276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213 eq2276
  have eq2292 : False := by grind
  exact eq2292

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_y_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq40 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))) ∨ (M.op X0 (M.op X0 (M.op X1 X0))) = (k X0 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 (M.op X0 (M.op X1 X0)))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op X0 (M.op X1 X0)))
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))) ∨ (M.op X0 (M.op X0 (M.op X1 X0))) = (k X0 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq54 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq54
    | (have j0 := eq54 (σ X0) (σ X1)
       grind)
    | exact resolve eq54 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq54 X0 (τ X1)
       grind)
    | exact superpose eq54 eq18
    | (have j1 := eq54 X0 (τ X1)
       grind)
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq54 X0 (σ X1)
       grind)
    | exact superpose eq54 eq22
    | (have j1 := eq54 X0 (σ X1)
       grind)
    | exact resolve eq22 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq54
  have eq79 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 x y
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 x y
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (M.op (σ X1) (M.op (σ X1) (σ (k X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X1) (σ X0)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq9
    | (have j1 := eq65 X0 X1
       grind)
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq65 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq65 X1 X1
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq82 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq82 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq153 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (M.op (σ X1) (σ (k X0 X1)))) = (k (σ X1) (M.op (σ X1) (M.op (σ X1) (σ (k X0 X1))))) ∨ (M.op (σ X1) (M.op (σ X1) (σ (k X0 X1)))) = (M.op (M.op (σ X1) (M.op (σ X1) (σ (k X0 X1)))) (M.op (σ X1) (M.op (σ X1) (σ (k X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq41 (σ X1) (σ X0)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq41
    | (have j1 := eq65 X0 X1
       grind)
    | exact resolve eq41 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq65
  have eq187 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71
    | exact resolve eq71 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq201 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq187
    | (have j0 := eq187 X0 X1
       grind)
    | exact resolve eq187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq204 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq201 X0 X0
       grind)
    | exact superpose eq201 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq201 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq201 X0 X0
       grind)
    | exact resolve eq12 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq201 X1 X0
       grind)
    | exact superpose eq201 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq201 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq201 X0 X1
       grind)
    | exact resolve eq13 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq218 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq204 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq415 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq83
    | (have j0 := eq83 (τ X0) (τ X1)
       grind)
    | exact resolve eq83 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq428 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq415 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq415
    | (have j0 := eq415 X0 X1
       grind)
    | exact resolve eq415 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq433 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq428 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq428
    | (have j0 := eq428 X0 X1
       grind)
    | exact resolve eq428 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq437 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq433 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq433
    | (have j0 := eq433 X0 X1
       grind)
    | exact resolve eq433 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq441 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq437 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq437
    | (have j0 := eq437 X0 X1
       grind)
    | exact resolve eq437 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq506 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) X0) ∨ (M.op X0 (M.op X0 (M.op X0 (σ (k X1 (τ X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ (k x y))))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq519 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (k (σ X1) X0)))) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq506 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq506
    | (have j0 := eq506 X0 X1
       grind)
    | exact resolve eq506 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq657 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) = (k (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0))))) ∨ (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) = (M.op (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq153 X0 X0
       grind)
    | exact superpose eq153 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq153 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq153 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op (σ X1) (M.op (σ X1) (σ (k X0 X1))))
       have r₂ := eq153 X0 X1
       grind)
    | exact resolve eq12 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq665 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) = (k (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0))))) ∨ (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) = (M.op (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0))))) := by
    intro X0 X1
    first
    | (have j0 := eq657 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq933 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq72
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq958 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq933 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq933
    | (have j0 := eq933 X0 X1
       grind)
    | exact resolve eq933 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq933
  have eq997 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq958 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq958
    | (have j0 := eq958 (σ X1) (σ X0)
       grind)
    | exact resolve eq958 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1044 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq997 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq997
    | (have j0 := eq997 X0 X1
       grind)
    | exact resolve eq997 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1093 : ∀ X0 X1 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq218 X0 X1
       grind)
    | exact superpose eq218 eq10
    | (have j1 := eq218 X0 X1
       grind)
    | exact resolve eq10 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1136 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1093 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1093
    | (have j0 := eq1093 X0 X0
       grind)
    | exact resolve eq1093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1169 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1136 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1170 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1169 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1188 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X1 (k X0 X1)))) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq519 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq519
    | exact resolve eq519 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq1227 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq1170 X0
       grind)
    | exact superpose eq1170 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1241 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1170 (σ X0)
       grind)
    | exact superpose eq1170 eq15
    | exact resolve eq15 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1262 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1241 X0
       have i₂ := eq1170 X0
       grind)
    | exact superpose eq1170 eq1241
    | exact resolve eq1241 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1608 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq1262 X0
       grind)
    | exact superpose eq1262 eq9
    | exact resolve eq9 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2549 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ (k x y))))) ∨ (σ (M.op x y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq510
       have i₂ := eq201 y x
       grind)
    | exact superpose eq201 eq510
    | (have j1 := eq201 (M.op (σ y) (M.op (σ y) (σ (k x y)))) (σ y)
       grind)
    | exact resolve eq510 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq510
  have eq2550 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ (k x y))))) ∨ (σ (M.op x y)) = (σ (k x y)) := by grind
  clear eq2549
  have eq4553 : (σ (M.op x y)) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1044 x y
       grind)
    | exact superpose eq1044 eq16
    | (have j1 := eq1044 x y
       grind)
    | exact resolve eq16 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq6298 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X2 X0) = X0 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq217 X2 X0
       grind)
    | exact superpose eq217 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq217 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq217 X0 X1
       grind)
    | exact resolve eq12 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq6324 : ∀ X0 X1 X2 : G, (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ (k X2 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6298 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6298
  have eq27609 : ∀ X0 X1 X2 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq6324 X1 X2 X0
       grind)
    | exact superpose eq6324 eq10
    | (have j1 := eq6324 X1 X2 X0
       grind)
    | exact resolve eq10 eq6324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6324
  have eq27789 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27609 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq27609
    | (have j0 := eq27609 X0 X1 X0
       grind)
    | exact resolve eq27609 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27609
  have eq28262 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq27789 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27789
  have eq28263 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28262 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28262
  have eq28668 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq28263 (σ X0) X1
       grind)
    | exact superpose eq28263 eq29
    | (have j1 := eq28263 (σ X0) X1
       grind)
    | exact resolve eq29 eq28263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq28708 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq28263 (τ X0) X1
       grind)
    | exact superpose eq28263 eq17
    | (have j1 := eq28263 (τ X0) X1
       grind)
    | exact resolve eq17 eq28263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq28263
  have eq30845 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq28708 X1 (τ X0)
       grind)
    | exact superpose eq28708 eq18
    | (have j1 := eq28708 X1 (τ X0)
       grind)
    | exact resolve eq18 eq28708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq28708
  have eq30907 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30845 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq30845
    | (have j0 := eq30845 X0 X1
       grind)
    | exact resolve eq30845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30845
  have eq30963 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30907 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30907
    | (have j0 := eq30907 X0 X1
       grind)
    | exact resolve eq30907 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30907
  have eq30995 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30963 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30963
    | (have j0 := eq30963 X0 X1
       grind)
    | exact resolve eq30963 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30963
  have eq31631 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30995 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30995
    | (have j0 := eq30995 X1 (σ X0)
       grind)
    | exact resolve eq30995 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30995
  have eq32330 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) = (k (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) = (M.op (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 X1
       have i₂ := eq1170 X0
       grind)
    | exact superpose eq1170 eq665
    | (have j0 := eq665 X0 X1
       grind)
    | exact resolve eq665 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq32331 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) ∨ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) = (k (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32330 X0 X1
       have i₂ := eq1170 X0
       grind)
    | exact superpose eq1170 eq32330
    | (have j0 := eq32330 X0 X1
       grind)
    | exact resolve eq32330 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32330
  have eq33503 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31631 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31631
    | (have j0 := eq31631 X1 (σ X0)
       grind)
    | exact resolve eq31631 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31631
  have eq33738 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33503 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq33503
    | (have j0 := eq33503 X0 X1
       grind)
    | exact resolve eq33503 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33503
  have eq33755 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33738 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq33738
    | (have j0 := eq33738 X0 X1
       grind)
    | exact resolve eq33738 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33738
  have eq34726 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq33755 y x
       grind)
    | exact superpose eq33755 eq79
    | (have j1 := eq33755 y x
       grind)
    | (have r₁ := eq79
       have r₂ := eq33755 y x
       grind)
    | exact resolve eq79 eq33755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq34898 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq33755 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33755
  have eq34899 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq34726
  have eq35426 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34899
       grind)
    | exact superpose eq34899 eq16
    | exact resolve eq16 eq34899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35432 : (τ (σ x)) = (k x (τ (σ y))) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq28668 x (σ y)
       have i₂ := eq34899
       grind)
    | exact superpose eq34899 eq28668
    | (have j0 := eq28668 x (σ y)
       grind)
    | exact resolve eq28668 eq34899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28668 eq34899
  have eq35462 : (k x y) = (τ (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq35432
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq35432
    | exact resolve eq35432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35432
  have eq35471 : x = (k x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq35462
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35462
    | exact resolve eq35462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35462
  have eq35473 : (σ y) = (σ (k x y)) ∨ x = (k x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq35471
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq35471
    | exact resolve eq35471 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35471
  have eq35474 : x = (k x y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq35473
  have eq36014 : x ≠ x ∨ x = (M.op x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq441 x y
       have i₂ := eq35474
       grind)
    | exact superpose eq35474 eq441
    | (have j0 := eq441 x y
       grind)
    | (have r₁ := eq441 x y
       have r₂ := eq35474
       grind)
    | exact resolve eq441 eq35474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35474
  have eq36068 : x = (M.op x y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq36014
  have eq37299 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq35426
       have i₂ := eq36068
       grind)
    | exact superpose eq36068 eq35426
    | exact resolve eq35426 eq36068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35426 eq36068
  have eq37304 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq37299
  have eq37305 : (σ y) = (σ (k x y)) := by grind
  clear eq37304
  have eq37511 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq37305
       grind)
    | exact superpose eq37305 eq10
    | exact resolve eq10 eq37305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37718 : y = (k x y) := by
    first
    | (have i₁ := eq37511
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq37511
    | exact resolve eq37511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37511
  have eq37977 : x = (M.op x y) ∨ y = (M.op y (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq1188 x y
       have i₂ := eq37718
       grind)
    | exact superpose eq37718 eq1188
    | (have j0 := eq1188 x y
       grind)
    | exact resolve eq1188 eq37718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq42319 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq4553
       have i₂ := eq37977
       grind)
    | exact superpose eq37977 eq4553
    | exact resolve eq4553 eq37977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4553 eq37977
  have eq42344 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y (M.op y (M.op y y))) := by grind
  clear eq42319
  have eq42349 : y = (M.op y (M.op y (M.op y y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq42344
       have i₂ := eq37718
       grind)
    | exact superpose eq37718 eq42344
    | exact resolve eq42344 eq37718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37718 eq42344
  have eq71664 : y = (M.op y y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq42349
       grind)
    | exact superpose eq42349 eq9
    | exact resolve eq9 eq42349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42349
  have eq72146 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1227 y X0
       have i₂ := eq71664
       grind)
    | exact superpose eq71664 eq1227
    | (have j0 := eq1227 y X0
       grind)
    | exact resolve eq1227 eq71664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq72221 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq34898 y y
       have i₂ := eq71664
       grind)
    | exact superpose eq71664 eq34898
    | (have j0 := eq34898 y y
       grind)
    | exact resolve eq34898 eq71664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34898 eq71664
  have eq72222 : (σ y) = (σ (k y y)) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq72221
  have eq72227 : ∀ X0 : G, y = (τ (M.op (σ x) (σ y))) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq72146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72146
  have eq72230 : y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq72222
       have i₂ := eq1170 y
       grind)
    | exact superpose eq1170 eq72222
    | exact resolve eq72222 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170 eq72222
  have eq74526 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq72230
       grind)
    | exact superpose eq72230 eq11
    | exact resolve eq11 eq72230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72230
  have eq76127 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74526
       grind)
    | exact superpose eq74526 eq16
    | exact resolve eq16 eq74526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74526
  have eq83197 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq72227 X0
       grind)
    | exact superpose eq72227 eq11
    | (have j1 := eq72227 X0
       grind)
    | exact resolve eq11 eq72227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72227
  have eq84629 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq83197 X0
       grind)
    | exact superpose eq83197 eq16
    | (have j1 := eq83197 X0
       grind)
    | exact resolve eq16 eq83197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83197
  have eq102360 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ (σ (M.op x y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq2550
       have i₂ := eq37305
       grind)
    | exact superpose eq37305 eq2550
    | exact resolve eq2550 eq37305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550
  have eq102361 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) ∨ (σ (M.op x y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq102360
       have i₂ := eq1262 y
       grind)
    | exact superpose eq1262 eq102360
    | exact resolve eq102360 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102360
  have eq102362 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq102361
       have i₂ := eq37305
       grind)
    | exact superpose eq37305 eq102361
    | exact resolve eq102361 eq37305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37305 eq102361
  have eq102645 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq32331 y x
       have i₂ := eq102362
       grind)
    | exact superpose eq102362 eq32331
    | (have j0 := eq32331 y X0
       grind)
    | exact resolve eq32331 eq102362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32331
  have eq102647 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1608 y
       have i₂ := eq102362
       grind)
    | exact superpose eq102362 eq1608
    | exact resolve eq1608 eq102362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608 eq102362
  have eq102783 : (σ y) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq102647
       have i₂ := eq1262 y
       grind)
    | exact superpose eq1262 eq102647
    | exact resolve eq102647 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262 eq102647
  have eq102785 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq102645 X0
       have j1 := eq441 (σ y) (σ y)
       grind)
    | (have r₁ := eq102645 X0
       have r₂ := eq441 (σ y) (σ y)
       grind)
    | exact resolve eq102645 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq102645
  have eq102822 : (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq102783
       have r₂ := eq76127
       grind)
    | exact resolve eq102783 eq76127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76127 eq102783
  have eq102824 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq102785 X0
       have j1 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq102785 X0
       have r₂ := eq12 X0 (σ y)
       grind)
    | exact resolve eq102785 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102785
  have eq102847 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq102824 X0
       have j1 := eq84629 X0
       grind)
    | (have r₁ := eq102824 X0
       have r₂ := eq84629 X0
       grind)
    | exact resolve eq102824 eq84629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84629 eq102824
  have eq102868 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq102822
       grind)
    | exact superpose eq102822 eq10
    | exact resolve eq10 eq102822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102822
  have eq103240 : y = (M.op y y) := by
    first
    | (have i₁ := eq102868
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq102868
    | exact resolve eq102868 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102868
  have eq104168 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq103240
       grind)
    | exact superpose eq103240 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq103240
       grind)
    | exact resolve eq12 eq103240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103240
  have eq104266 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq104168 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104168
  have eq109487 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq102847 (σ X0)
       grind)
    | exact superpose eq102847 eq15
    | exact resolve eq15 eq102847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102847
  have eq109668 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq109487 X0
       have i₂ := eq104266 X0
       grind)
    | exact superpose eq104266 eq109487
    | exact resolve eq109487 eq104266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104266 eq109487
  have eq116759 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq109668 x
       grind)
    | exact superpose eq109668 eq16
    | (have r₁ := eq16
       have r₂ := eq109668 x
       grind)
    | exact resolve eq16 eq109668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109668
  have eq116972 : False := by grind
  exact eq116972
