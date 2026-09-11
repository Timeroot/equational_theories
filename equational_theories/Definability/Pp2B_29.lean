import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = X1 ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X1
       have i₂ := eq14 X2 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 (M.op X0 X1)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq66 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq86 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq96 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq9
    | exact resolve eq9 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq171 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq96
    | exact resolve eq96 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq226 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq171 X0 X1
       grind)
    | exact superpose eq171 eq9
    | exact resolve eq9 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op X0 X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (M.op X0 X1) X0 X2 X3
       have i₂ := eq171 X0 X1
       grind)
    | exact superpose eq171 eq24
    | exact resolve eq24 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq456 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq60 x y
       grind)
    | exact superpose eq60 eq16
    | (have j1 := eq60 x x
       grind)
    | exact resolve eq16 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq606 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 (M.op X0 X1)) X2) = (k X2 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (M.op X0 X2) X0 X2
       have i₂ := eq59 X0 (M.op X0 X2) X2
       grind)
    | exact superpose eq59 eq33
    | (have j1 := eq59 X0 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq33 (M.op X0 X2) X0 X2
       have r₂ := eq59 X0 (M.op X0 X2) X2
       grind)
    | exact resolve eq33 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq59
  have eq632 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 (M.op X0 X1)) X2) = (k X2 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq606 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq638 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq632 X0 X1 X2
       have i₂ := eq171 X0 X1
       grind)
    | exact superpose eq171 eq632
    | (have j0 := eq632 X0 X1 X2
       grind)
    | exact resolve eq632 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq645 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq638 X0 X1 X2
       have i₂ := eq171 X0 X1
       grind)
    | exact superpose eq171 eq638
    | (have j0 := eq638 X0 X1 X2
       grind)
    | exact resolve eq638 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq7602 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq456
       have i₂ := eq66 x y
       grind)
    | exact superpose eq66 eq456
    | (have j1 := eq66 x y
       grind)
    | exact resolve eq456 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq456
  have eq7603 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq7602
  have eq25788 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq645 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq25789 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq25788 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25788
  have eq25811 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq25789 X0 X1
       have j1 := eq12 (M.op X0 X1) (M.op X0 X1)
       grind)
    | (have r₁ := eq25789 X0 X1
       have r₂ := eq12 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq25789 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25789
  have eq25880 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq25811 (M.op (M.op (M.op (M.op X0 x) (M.op X0 x)) x) (M.op X0 x)) x
       have i₂ := eq231 X0 x x x
       grind)
    | exact superpose eq231 eq25811
    | exact resolve eq25811 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq25811
  have eq26563 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq25880 (σ X0)
       grind)
    | exact superpose eq25880 eq15
    | exact resolve eq15 eq25880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26571 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq25880 (τ X0)
       grind)
    | exact superpose eq25880 eq34
    | exact resolve eq34 eq25880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq26604 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq26571 X0
       have i₂ := eq25880 X0
       grind)
    | exact superpose eq25880 eq26571
    | exact resolve eq26571 eq25880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26571
  have eq26610 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq26563 X0
       have i₂ := eq25880 X0
       grind)
    | exact superpose eq25880 eq26563
    | exact resolve eq26563 eq25880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26563
  have eq27006 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq26604 X0
       grind)
    | exact superpose eq26604 eq9
    | exact resolve eq9 eq26604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26604
  have eq27532 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq26610 X0
       grind)
    | exact superpose eq26610 eq9
    | exact resolve eq9 eq26610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32941 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (σ X0)) X1) (σ (σ (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27532 (σ X0) X1
       have i₂ := eq26610 X0
       grind)
    | exact superpose eq26610 eq27532
    | exact resolve eq27532 eq26610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27532
  have eq145815 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq171 (σ x) (σ y)
       have i₂ := eq7603
       grind)
    | exact superpose eq7603 eq171
    | exact resolve eq171 eq7603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7603
  have eq145906 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq145815
  have eq145955 : (σ x) = (σ (M.op x x)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq145906
       have i₂ := eq26610 x
       grind)
    | exact superpose eq26610 eq145906
    | exact resolve eq145906 eq26610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26610 eq145906
  have eq146062 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq145955
       have i₂ := eq25880 x
       grind)
    | exact superpose eq25880 eq145955
    | exact resolve eq145955 eq25880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25880 eq145955
  have eq168557 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq146062
       grind)
    | exact superpose eq146062 eq10
    | exact resolve eq10 eq146062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146062
  have eq168734 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq168557
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq168557
    | exact resolve eq168557 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168557
  have eq168735 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq168734
  have eq169921 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq171 x y
       have i₂ := eq168735
       grind)
    | exact superpose eq168735 eq171
    | exact resolve eq171 eq168735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168735
  have eq170015 : x = (M.op x x) := by grind
  clear eq169921
  have eq171123 : ∀ X0 : G, (M.op (M.op (M.op (τ x) X0) (τ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27006 x X0
       have i₂ := eq170015
       grind)
    | exact superpose eq170015 eq27006
    | exact resolve eq27006 eq170015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27006
  have eq171186 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq170015
       grind)
    | exact superpose eq170015 eq9
    | exact resolve eq9 eq170015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171268 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq226 x x x
       have i₂ := eq170015
       grind)
    | exact superpose eq170015 eq226
    | exact resolve eq226 eq170015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170015
  have eq171375 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq171268 X0
       have i₂ := eq171 x X0
       grind)
    | exact superpose eq171 eq171268
    | exact resolve eq171268 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq171268
  have eq175151 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq171186 X0
       have i₂ := eq171375 X0
       grind)
    | exact superpose eq171375 eq171186
    | exact resolve eq171186 eq171375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175326 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X1) = (M.op (M.op (M.op (M.op (M.op x X0) x) X1) X0) (M.op (M.op (M.op x X0) x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226 (M.op (M.op x X0) x) X1 X0
       have i₂ := eq171186 X0
       grind)
    | exact superpose eq171186 eq226
    | exact resolve eq226 eq171186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq171186
  have eq175499 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq175326 X0 X1
       have i₂ := eq171375 X0
       grind)
    | exact superpose eq171375 eq175326
    | exact resolve eq175326 eq171375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171375 eq175326
  have eq175602 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq175499 X0 X0
       have i₂ := eq175151 X0
       grind)
    | exact superpose eq175151 eq175499
    | exact resolve eq175499 eq175151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175499
  have eq210022 : ∀ X0 : G, (M.op (τ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq171123 X0
       have i₂ := eq175602 X0 (τ x)
       grind)
    | exact superpose eq175602 eq171123
    | exact resolve eq171123 eq175602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171123
  have eq211721 : ∀ X0 : G, (M.op (M.op (M.op (σ (σ (τ x))) X0) (σ (σ (τ x)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32941 (τ x) X0
       have i₂ := eq210022 (τ x)
       grind)
    | exact superpose eq210022 eq32941
    | exact resolve eq32941 eq210022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32941 eq210022
  have eq212172 : ∀ X0 : G, (M.op (σ (σ (τ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq211721 X0
       have i₂ := eq175602 X0 (σ (σ (τ x)))
       grind)
    | exact superpose eq175602 eq211721
    | exact resolve eq211721 eq175602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175602 eq211721
  have eq212230 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq212172 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq212172
    | exact resolve eq212172 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212172
  have eq213612 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq212230 (σ y)
       grind)
    | exact superpose eq212230 eq16
    | exact resolve eq16 eq212230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212230
  have eq214142 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq213612
       have i₂ := eq175151 y
       grind)
    | exact superpose eq175151 eq213612
    | exact resolve eq213612 eq175151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175151 eq213612
  have eq214143 : False := by grind
  exact eq214143

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq89 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq97 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq9
    | exact resolve eq9 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq131 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq97
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq131 X0 X1
       grind)
    | exact superpose eq131 eq9
    | exact resolve eq9 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq176 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq161 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq161
    | (have j0 := eq161 X0
       grind)
    | exact resolve eq161 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq161
  have eq177 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq176
    | (have j0 := eq176 X0
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq178 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq177 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq177 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq177 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq181 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq178 (σ X0)
       grind)
    | exact superpose eq178 eq15
    | exact resolve eq15 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq181 X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq181
    | exact resolve eq181 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq181
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 (σ X0) X1
       have i₂ := eq192 X0
       grind)
    | exact superpose eq192 eq97
    | exact resolve eq97 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq228 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2815 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq228
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq228
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq228
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq228
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq228 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq2816 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq2815
  have eq30590 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2816
       grind)
    | exact superpose eq2816 eq16
    | exact resolve eq16 eq2816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2816
  have eq30591 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq30590
       have r₂ := eq192 x
       grind)
    | exact resolve eq30590 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30590
  have eq30638 : (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq131 y x
       have i₂ := eq30591
       grind)
    | exact superpose eq30591 eq131
    | exact resolve eq131 eq30591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30591
  have eq30702 : y = (τ (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30638
       grind)
    | exact superpose eq30638 eq10
    | exact resolve eq10 eq30638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30638
  have eq30812 : x = y ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq30702
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30702
    | exact resolve eq30702 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30702
  have eq31170 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30812
       grind)
    | exact superpose eq30812 eq16
    | exact resolve eq16 eq30812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30812
  have eq31171 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq31170
       have r₂ := eq192 x
       grind)
    | exact resolve eq31170 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31170
  have eq31249 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq131 (σ y) (σ x)
       have i₂ := eq31171
       grind)
    | exact superpose eq31171 eq131
    | exact resolve eq131 eq31171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31171
  have eq31286 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31249
       have i₂ := eq192 y
       grind)
    | exact superpose eq192 eq31249
    | exact resolve eq31249 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq31249
  have eq31884 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq31286
       grind)
    | exact superpose eq31286 eq10
    | exact resolve eq10 eq31286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31286
  have eq31996 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31884
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq31884
    | exact resolve eq31884 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31884
  have eq31997 : y = (M.op y y) := by grind
  clear eq31996
  have eq32498 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq217 y X0
       have i₂ := eq31997
       grind)
    | exact superpose eq31997 eq217
    | exact resolve eq217 eq31997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq32583 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq31997
       grind)
    | exact superpose eq31997 eq9
    | exact resolve eq9 eq31997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32629 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq150 y y x
       have i₂ := eq31997
       grind)
    | exact superpose eq31997 eq150
    | exact resolve eq150 eq31997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31997
  have eq32666 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq32629 X0
       have i₂ := eq131 y X0
       grind)
    | exact superpose eq131 eq32629
    | exact resolve eq32629 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq32629
  have eq33175 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32583 X0
       have i₂ := eq32666 X0
       grind)
    | exact superpose eq32666 eq32583
    | exact resolve eq32583 eq32666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33271 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) y) X1) = (M.op (M.op (M.op (M.op (M.op y X0) y) X1) X0) (M.op (M.op (M.op y X0) y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150 (M.op (M.op y X0) y) X1 X0
       have i₂ := eq32583 X0
       grind)
    | exact superpose eq32583 eq150
    | exact resolve eq150 eq32583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq32583
  have eq33315 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33271 X0 X1
       have i₂ := eq32666 X0
       grind)
    | exact superpose eq32666 eq33271
    | exact resolve eq33271 eq32666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33271
  have eq33371 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33315 X0 X0
       have i₂ := eq33175 X0
       grind)
    | exact superpose eq33175 eq33315
    | exact resolve eq33315 eq33175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33315
  have eq33596 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq32666 X0
       have i₂ := eq33175 X0
       grind)
    | exact superpose eq33175 eq32666
    | exact resolve eq32666 eq33175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32666 eq33175
  have eq47148 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq33371 X0 (M.op (M.op (σ y) X0) (σ y))
       have i₂ := eq32498 X0
       grind)
    | exact superpose eq32498 eq33371
    | exact resolve eq33371 eq32498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32498
  have eq47164 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq47148 X0
       have i₂ := eq33371 X0 (σ y)
       grind)
    | exact superpose eq33371 eq47148
    | exact resolve eq47148 eq33371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33371 eq47148
  have eq49566 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47164 (σ x)
       grind)
    | exact superpose eq47164 eq16
    | exact resolve eq16 eq47164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47164
  have eq49672 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq49566
       have i₂ := eq33596 x
       grind)
    | exact superpose eq33596 eq49566
    | exact resolve eq49566 eq33596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33596 eq49566
  have eq49673 : False := by grind
  exact eq49673

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq43 (σ X0)
       grind)
    | exact superpose eq43 eq15
    | exact resolve eq15 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq19
    | exact resolve eq19 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
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
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq57
    | exact resolve eq57 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq63
    | exact resolve eq63 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq63
  have eq79 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq145 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 y x
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq185 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq116 (τ X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq116
    | exact resolve eq116 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq116
  have eq203 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq185 X0
       grind)
    | exact superpose eq185 eq9
    | exact resolve eq9 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq353 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op (σ X0) (σ X0))) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq203 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq203
    | exact resolve eq203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq365 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (σ (M.op X0 X0))) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq353 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq353
    | exact resolve eq353 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq367 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq365
    | exact resolve eq365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq412 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq367
    | exact resolve eq367 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq412 X0 X1
       grind)
    | exact superpose eq412 eq9
    | exact resolve eq9 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq145
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq145
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq145
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq145
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq145 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq672 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq671
  have eq8778 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq672
       grind)
    | exact superpose eq672 eq16
    | exact resolve eq16 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq8779 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8778
       have r₂ := eq66 x
       grind)
    | exact resolve eq8778 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8778
  have eq41611 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq412 x y
       have i₂ := eq8779
       grind)
    | exact superpose eq8779 eq412
    | exact resolve eq412 eq8779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8779
  have eq67152 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq412 (σ x) (σ y)
       have i₂ := eq41611
       grind)
    | exact superpose eq41611 eq412
    | exact resolve eq412 eq41611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41611
  have eq67201 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq67152
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq67152
    | exact resolve eq67152 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67152
  have eq68130 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq67201
       grind)
    | exact superpose eq67201 eq10
    | exact resolve eq10 eq67201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67201
  have eq68312 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq68130
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq68130
    | exact resolve eq68130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68130
  have eq68753 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68312
       grind)
    | exact superpose eq68312 eq16
    | exact resolve eq16 eq68312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68312
  have eq68754 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq68753
       have r₂ := eq66 x
       grind)
    | exact resolve eq68753 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq68753
  have eq68783 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq68754
       grind)
    | exact superpose eq68754 eq10
    | exact resolve eq10 eq68754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68754
  have eq68967 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq68783
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq68783
    | exact resolve eq68783 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68783
  have eq68968 : x = (M.op x x) := by grind
  clear eq68967
  have eq68987 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq91 x X0
       have i₂ := eq68968
       grind)
    | exact superpose eq68968 eq91
    | exact resolve eq91 eq68968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq69014 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq367 x X0
       have i₂ := eq68968
       grind)
    | exact superpose eq68968 eq367
    | exact resolve eq367 eq68968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq69128 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq552 x x x
       have i₂ := eq68968
       grind)
    | exact superpose eq68968 eq552
    | exact resolve eq552 eq68968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68968
  have eq69157 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq69128 X0
       have i₂ := eq412 x X0
       grind)
    | exact superpose eq412 eq69128
    | exact resolve eq69128 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq69128
  have eq71181 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq69014 X0
       have i₂ := eq69157 X0
       grind)
    | exact superpose eq69157 eq69014
    | exact resolve eq69014 eq69157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69014 eq69157
  have eq71727 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq552 x X1 X0
       have i₂ := eq71181 X0
       grind)
    | exact superpose eq71181 eq552
    | exact resolve eq552 eq71181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq71919 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71727 X0 X0
       have i₂ := eq71181 X0
       grind)
    | exact superpose eq71181 eq71727
    | exact resolve eq71727 eq71181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71727
  have eq107404 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68987 X0
       have i₂ := eq71919 X0 (σ x)
       grind)
    | exact superpose eq71919 eq68987
    | exact resolve eq68987 eq71919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68987 eq71919
  have eq107475 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq107404 (σ y)
       grind)
    | exact superpose eq107404 eq16
    | exact resolve eq16 eq107404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107404
  have eq108027 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq107475
       have i₂ := eq71181 y
       grind)
    | exact superpose eq71181 eq107475
    | exact resolve eq107475 eq71181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71181 eq107475
  have eq108028 : False := by grind
  exact eq108028

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyy_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq89 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq97 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq9
    | exact resolve eq9 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq131 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq97
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq131 X0 X1
       grind)
    | exact superpose eq131 eq9
    | exact resolve eq9 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq176 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq161 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq161
    | (have j0 := eq161 X0
       grind)
    | exact resolve eq161 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq161
  have eq177 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq176
    | (have j0 := eq176 X0
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq178 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq177 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq177 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq177 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq181 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq178 (σ X0)
       grind)
    | exact superpose eq178 eq15
    | exact resolve eq15 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq181 X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq181
    | exact resolve eq181 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq181
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 (σ X0) X1
       have i₂ := eq192 X0
       grind)
    | exact superpose eq192 eq97
    | exact resolve eq97 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq228 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3081 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq228
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq228
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq228
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq228
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq228 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq3082 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3081
  have eq29066 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3082
       grind)
    | exact superpose eq3082 eq16
    | exact resolve eq16 eq3082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3082
  have eq29067 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq29066
       have r₂ := eq192 x
       grind)
    | exact resolve eq29066 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29066
  have eq29114 : (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq131 x y
       have i₂ := eq29067
       grind)
    | exact superpose eq29067 eq131
    | exact resolve eq131 eq29067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29067
  have eq29165 : y = (τ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq29114
       grind)
    | exact superpose eq29114 eq10
    | exact resolve eq10 eq29114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29114
  have eq29270 : x = y ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29165
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29165
    | exact resolve eq29165 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29165
  have eq29667 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29270
       grind)
    | exact superpose eq29270 eq16
    | exact resolve eq16 eq29270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29270
  have eq29668 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq29667
       have r₂ := eq192 x
       grind)
    | exact resolve eq29667 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29667
  have eq29740 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq131 (σ x) (σ y)
       have i₂ := eq29668
       grind)
    | exact superpose eq29668 eq131
    | exact resolve eq131 eq29668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29668
  have eq29769 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29740
       have i₂ := eq192 x
       grind)
    | exact superpose eq192 eq29740
    | exact resolve eq29740 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq29740
  have eq30263 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq29769
       grind)
    | exact superpose eq29769 eq10
    | exact resolve eq10 eq29769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29769
  have eq30368 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq30263
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30263
    | exact resolve eq30263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30263
  have eq30369 : x = (M.op x x) := by grind
  clear eq30368
  have eq30540 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq217 x X0
       have i₂ := eq30369
       grind)
    | exact superpose eq30369 eq217
    | exact resolve eq217 eq30369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq30593 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq30369
       grind)
    | exact superpose eq30369 eq9
    | exact resolve eq9 eq30369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30639 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq150 x x x
       have i₂ := eq30369
       grind)
    | exact superpose eq30369 eq150
    | exact resolve eq150 eq30369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30369
  have eq30665 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq30639 X0
       have i₂ := eq131 x X0
       grind)
    | exact superpose eq131 eq30639
    | exact resolve eq30639 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq30639
  have eq30997 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30593 X0
       have i₂ := eq30665 X0
       grind)
    | exact superpose eq30665 eq30593
    | exact resolve eq30593 eq30665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31073 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X1) = (M.op (M.op (M.op (M.op (M.op x X0) x) X1) X0) (M.op (M.op (M.op x X0) x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150 (M.op (M.op x X0) x) X1 X0
       have i₂ := eq30593 X0
       grind)
    | exact superpose eq30593 eq150
    | exact resolve eq150 eq30593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq30593
  have eq31109 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31073 X0 X1
       have i₂ := eq30665 X0
       grind)
    | exact superpose eq30665 eq31073
    | exact resolve eq31073 eq30665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30665 eq31073
  have eq31149 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31109 X0 X0
       have i₂ := eq30997 X0
       grind)
    | exact superpose eq30997 eq31109
    | exact resolve eq31109 eq30997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31109
  have eq36043 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30540 X0
       have i₂ := eq31149 X0 (σ x)
       grind)
    | exact superpose eq31149 eq30540
    | exact resolve eq30540 eq31149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30540 eq31149
  have eq36492 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36043 (σ y)
       grind)
    | exact superpose eq36043 eq16
    | exact resolve eq16 eq36043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36043
  have eq36750 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq36492
       have i₂ := eq30997 y
       grind)
    | exact superpose eq30997 eq36492
    | exact resolve eq36492 eq30997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30997 eq36492
  have eq36751 : False := by grind
  exact eq36751

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq175 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 y
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq185 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq190 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq187 eq16
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq182 eq185
    | exact resolve eq185 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq185
  have eq563 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq559
       grind)
    | exact superpose eq559 eq16
    | exact resolve eq16 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq569 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq187 eq190
    | exact resolve eq190 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq190
  have eq581 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq563 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq563
    | exact resolve eq563 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq587 : (M.op y y) = (k (M.op y y) y) := by
    first
    | (have i₁ := eq181 y
       have i₂ := eq581 y
       grind)
    | exact superpose eq581 eq181
    | exact resolve eq181 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
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
  have eq655 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq699 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq641
       grind)
    | exact superpose eq641 eq40
    | exact resolve eq40 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq641
  have eq700 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq699
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq699
    | exact resolve eq699 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq702 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq700
    | exact resolve eq700 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq702 eq655
    | exact resolve eq655 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq719 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq712
       have r₂ := eq27
       grind)
    | exact resolve eq712 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq724 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq719 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq719
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq719
       grind)
    | exact resolve eq12 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq719 eq16
    | exact resolve eq16 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq724
  have eq730 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq702 eq728
    | exact resolve eq728 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq747 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq730 eq181
    | exact resolve eq181 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq730
  have eq749 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq747
    | exact resolve eq747 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq702 eq749
    | exact resolve eq749 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq749
  have eq752 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq751
       have r₂ := eq27
       grind)
    | exact resolve eq751 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq754 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq581 x
       have i₂ := eq752
       grind)
    | exact superpose eq752 eq581
    | exact resolve eq581 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq752
       grind)
    | exact superpose eq752 eq16
    | exact resolve eq16 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq760 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq758 X0
       have i₂ := eq581 X0
       grind)
    | exact superpose eq581 eq758
    | exact resolve eq758 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq797 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq760 y
       have i₂ := eq754
       grind)
    | exact superpose eq754 eq760
    | exact resolve eq760 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq806 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq797
  have eq822 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq806
       grind)
    | exact superpose eq806 eq16
    | exact resolve eq16 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq827 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq760 eq822
    | exact resolve eq822 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq822
  have eq897 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq827 y
       grind)
    | exact superpose eq827 eq18
    | (have j1 := eq827 y
       grind)
    | exact resolve eq18 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq916 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq897 eq29
    | exact resolve eq29 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq897
  have eq935 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq916
    | exact resolve eq916 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq916
  have eq936 : y = (M.op x y) := by grind
  clear eq935
  have eq946 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq936
       grind)
    | exact superpose eq936 eq18
    | exact resolve eq18 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq947 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq936
       grind)
    | exact superpose eq936 eq24
    | exact resolve eq24 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq949 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq936
       grind)
    | exact superpose eq936 eq41
    | exact resolve eq41 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq957 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq581 X0
       have i₂ := eq936
       grind)
    | exact superpose eq936 eq581
    | exact resolve eq581 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq958 : (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq587
       have i₂ := eq936
       grind)
    | exact superpose eq936 eq587
    | exact resolve eq587 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq966 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq947 eq20
    | exact resolve eq20 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq969 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq947 eq15
    | exact resolve eq15 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1258 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | exact superpose eq958 eq949
    | exact resolve eq949 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949 eq958
  have eq2927 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq719 eq726
    | exact resolve eq726 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2938 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq569 eq726
    | exact resolve eq726 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq726
  have eq2954 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq2927
  have eq2967 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq2938
       have i₂ := eq936
       grind)
    | exact superpose eq936 eq2938
    | exact resolve eq2938 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938
  have eq2972 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq2954
       have i₂ := eq936
       grind)
    | exact superpose eq936 eq2954
    | exact resolve eq2954 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954
  have eq2976 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2967 eq2972
    | exact resolve eq2972 eq2967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2967 eq2972
  have eq2999 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2976 eq719
    | exact resolve eq719 eq2976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq2976
  have eq3019 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq2999
       have i₂ := eq936
       grind)
    | exact superpose eq936 eq2999
    | exact resolve eq2999 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq2999
  have eq3020 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by grind
  clear eq3019
  have eq3033 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3020 eq957
    | exact resolve eq957 eq3020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3037 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq3020 eq16
    | exact resolve eq16 eq3020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3052 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq957 eq3037
    | exact resolve eq3037 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957 eq3037
  have eq3191 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3033 eq3052
    | exact resolve eq3052 eq3033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3033 eq3052
  have eq3218 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by grind
  clear eq3191
  have eq3225 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3020 eq3218
    | exact resolve eq3218 eq3020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3020 eq3218
  have eq3257 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3225 eq969
    | exact resolve eq969 eq3225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969 eq3225
  have eq3270 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq3257
    | exact resolve eq3257 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3257
  have eq3271 : x = (M.op x y) := by grind
  clear eq3270
  have eq3294 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq3271
       grind)
    | exact superpose eq3271 eq22
    | exact resolve eq22 eq3271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq3325 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq946
       have i₂ := eq3271
       grind)
    | exact superpose eq3271 eq946
    | exact resolve eq946 eq3271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946 eq3271
  have eq3359 : (σ x) = (σ y) := by
    first
    | exact superpose eq3294 eq947
    | exact resolve eq947 eq3294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq3360 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3294 eq20
    | exact resolve eq20 eq3294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3294
  have eq3386 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3359 eq26
    | exact resolve eq26 eq3359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3416 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
    first
    | exact superpose eq3359 eq1258
    | exact resolve eq1258 eq3359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq3430 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq3325 eq3416
    | exact resolve eq3416 eq3325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3325 eq3416
  have eq3445 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq3430
    | exact resolve eq3430 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3430
  have eq3458 : (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq966 eq3445
    | exact resolve eq3445 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq3445
  have eq3460 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3359 eq3458
    | exact resolve eq3458 eq3359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3359 eq3458
  have eq3579 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3386 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq3386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3386
  have eq3587 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3460 eq3579
    | exact resolve eq3579 eq3460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3460 eq3579
  have eq3588 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3587
  have eq3592 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq3588 eq27
    | exact resolve eq27 eq3588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3588
  have eq3609 : False := by grind
  exact eq3609

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_y_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq47 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq66 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq68 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq68
  have eq89 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq90 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq37
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq117 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq158 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq117 eq16
    | exact resolve eq16 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq209 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq381 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq388 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq381 X0
       grind)
    | exact superpose eq381 eq14
    | exact resolve eq14 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq65 X0 X0
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq65 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq709 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq708 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq713 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq1001 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq388
    | exact resolve eq388 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1004 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq388
    | exact resolve eq388 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1006 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51 eq388
    | exact resolve eq388 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq1109 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op sF2 x)
       have i₂ := eq1001 sF2 x
       grind)
    | exact superpose eq1001 eq51
    | exact resolve eq51 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq3777 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq709 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq709
    | (have j0 := eq709 (τ X0)
       grind)
    | exact resolve eq709 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq709
  have eq3785 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3777 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3777
    | (have j0 := eq3777 X0
       grind)
    | exact resolve eq3777 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777
  have eq3791 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3785 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3785
    | (have j0 := eq3785 X0
       grind)
    | exact resolve eq3785 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3785
  have eq6579 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq66 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq66
    | (have j0 := eq66 x
       grind)
    | exact resolve eq66 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq6601 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6579
  have eq6605 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6601
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq6601
    | exact resolve eq6601 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6601
  have eq29496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29506 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq29496
    | exact resolve eq29496 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29496
  have eq29517 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq29506
       have r₂ := eq28
       grind)
    | exact resolve eq29506 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29506
  have eq29519 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29517 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq29517
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq29517
       grind)
    | exact resolve eq12 eq29517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29520 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29517 eq14
    | exact resolve eq14 eq29517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29566 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29517 eq1001
    | exact resolve eq1001 eq29517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29569 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq29519
  have eq29570 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq29569
  have eq29595 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq29520 x
       have i₂ := eq1001 sF3 x
       grind)
    | exact superpose eq1001 eq29520
    | exact resolve eq29520 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29520
  have eq29613 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  have eq30058 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29613 eq107
    | exact resolve eq107 eq29613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq29613
  have eq30111 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq30058
    | exact resolve eq30058 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30058
  have eq30205 : (σ x) = (k (σ y) (σ x)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  have eq30253 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30111 eq1001
    | exact resolve eq1001 eq30111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30111
  have eq30258 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq30253
    | exact resolve eq30253 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30253
  have eq30346 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq713 y y
       have i₂ := eq30258
       grind)
    | exact superpose eq30258 eq713
    | (have j0 := eq713 y y
       grind)
    | exact resolve eq713 eq30258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30258
  have eq30351 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq30346
  have eq30352 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq30351
  have eq30367 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq30352
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30352
    | exact resolve eq30352 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30352
  have eq30668 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30367 eq14
    | exact resolve eq14 eq30367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30367
  have eq30735 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq30668 x
       have i₂ := eq1001 sF3 x
       grind)
    | exact superpose eq1001 eq30668
    | exact resolve eq30668 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30668
  have eq31002 : (τ (σ x)) = (k y x) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30205 eq99
    | exact resolve eq99 eq30205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq30205
  have eq31033 : y = (k y y) ∨ x = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq31002
    | exact resolve eq31002 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31002
  have eq32028 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq31033
       grind)
    | exact superpose eq31033 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq31033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31033
  have eq32048 : y = (M.op y y) ∨ x = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq32028
  have eq34271 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29570 eq101
    | exact resolve eq101 eq29570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29570
  have eq34291 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq34271
  have eq34322 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq34291
  have eq42354 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq34322 eq101
    | exact resolve eq101 eq34322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq34322
  have eq42374 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq42354
  have eq390628 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29566 eq29595
    | exact resolve eq29595 eq29566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29566 eq29595
  have eq390921 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq390628
  have eq391113 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq390921 eq381
    | exact resolve eq381 eq390921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390921
  have eq391216 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq391113
  have eq391235 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq391216 eq29517
    | exact resolve eq29517 eq391216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29517
  have eq391251 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq391216 eq30735
    | exact resolve eq30735 eq391216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30735 eq391216
  have eq391331 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq391251
  have eq391333 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq391235
  have eq391339 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq391331
    | exact resolve eq391331 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391331
  have eq391340 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq391339
  have eq391528 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq391340
       grind)
    | exact superpose eq391340 eq14
    | exact resolve eq14 eq391340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391638 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq391528 X0
       have i₂ := eq1001 y X0
       grind)
    | exact superpose eq1001 eq391528
    | exact resolve eq391528 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391528
  have eq394638 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq391638 x
       have i₂ := eq391340
       grind)
    | exact superpose eq391340 eq391638
    | exact resolve eq391638 eq391340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394937 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq394638
  have eq395141 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq381 x
       have i₂ := eq394937
       grind)
    | exact superpose eq394937 eq381
    | exact resolve eq381 eq394937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394937
  have eq395244 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq395141
  have eq395293 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq391340
       have i₂ := eq395244
       grind)
    | exact superpose eq395244 eq391340
    | exact resolve eq391340 eq395244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391340
  have eq395302 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq391638 x
       have i₂ := eq395244
       grind)
    | exact superpose eq395244 eq391638
    | exact resolve eq391638 eq395244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391638 eq395244
  have eq395374 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq395302
  have eq395380 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq395293
  have eq395584 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq395380
       grind)
    | exact superpose eq395380 eq72
    | exact resolve eq72 eq395380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq395380
  have eq395784 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq395584
  have eq395797 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq395784
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq395784
    | exact resolve eq395784 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395784
  have eq396993 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6605 eq395797
    | exact resolve eq395797 eq6605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6605 eq395797
  have eq399163 : x ≠ y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq395374
  have eq416025 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq396993 eq1001
    | exact resolve eq1001 eq396993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396993
  have eq416070 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq416025
    | exact resolve eq416025 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416025
  have eq416071 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq416070
  have eq416197 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq416071
  have eq416401 : (τ (σ x)) = (k x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq416197 eq56
    | exact resolve eq56 eq416197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq416197
  have eq416534 : x = (k x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq416401
    | exact resolve eq416401 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416401
  have eq416836 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq416534
       grind)
    | exact superpose eq416534 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq416534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416534
  have eq416858 : x = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq416836
  have eq416895 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq416858
       have r₂ := eq399163
       grind)
    | exact resolve eq416858 eq399163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399163 eq416858
  have eq417261 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq416895
  have eq417550 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq713 x x
       have i₂ := eq417261
       grind)
    | exact superpose eq417261 eq713
    | (have j0 := eq713 x x
       grind)
    | exact resolve eq713 eq417261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq417261
  have eq417557 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq417550
  have eq417558 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq417557
  have eq417594 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq417558
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq417558
    | exact resolve eq417558 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417558
  have eq417689 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq417594 eq48
    | exact resolve eq48 eq417594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq417712 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq417594 eq1109
    | exact resolve eq1109 eq417594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109 eq417594
  have eq417957 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1006 eq417712
    | exact resolve eq417712 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq417712
  have eq418898 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq417957 eq417689
    | exact resolve eq417689 eq417957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417689 eq417957
  have eq418976 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq418898
  have eq418977 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq418976
    | exact resolve eq418976 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq418976
  have eq418978 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq418977
  have eq418979 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq418978 eq28
    | exact resolve eq28 eq418978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq418978
  have eq484576 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq391333 eq42374
    | exact resolve eq42374 eq391333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42374 eq391333
  have eq484850 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq484576
  have eq484956 : y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq484850
       have r₂ := eq418979
       grind)
    | exact resolve eq484850 eq418979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484850
  have eq485014 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq484956
       grind)
    | exact superpose eq484956 eq14
    | exact resolve eq14 eq484956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485164 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq485014 X0
       have i₂ := eq1001 y X0
       grind)
    | exact superpose eq1001 eq485014
    | exact resolve eq485014 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485014
  have eq499868 : x = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq485164 x
       have i₂ := eq484956
       grind)
    | exact superpose eq484956 eq485164
    | exact resolve eq485164 eq484956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485164
  have eq500282 : y = (M.op x x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq499868
  have eq500558 : x = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq381 x
       have i₂ := eq500282
       grind)
    | exact superpose eq500282 eq381
    | exact resolve eq381 eq500282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq500282
  have eq500700 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq500558
  have eq500777 : x = y ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq484956
       have i₂ := eq500700
       grind)
    | exact superpose eq500700 eq484956
    | exact resolve eq484956 eq500700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484956 eq500700
  have eq500912 : y = (M.op x x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq500777
  have eq501130 : y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1001 x x
       have i₂ := eq500912
       grind)
    | exact superpose eq500912 eq1001
    | exact resolve eq1001 eq500912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq500912
  have eq501240 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq501130
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq501130
    | exact resolve eq501130 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501130
  have eq501246 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq501240 eq30
    | exact resolve eq30 eq501240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq501240
  have eq501892 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq501246
    | exact resolve eq501246 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501246
  have eq501893 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq501892
  have eq501908 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq501893 eq29
    | exact resolve eq29 eq501893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq501893
  have eq502610 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq501908
    | exact resolve eq501908 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501908
  have eq502624 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq502610 eq21
    | exact resolve eq21 eq502610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502610
  have eq503649 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq502624
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq502624
    | exact resolve eq502624 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502624
  have eq503650 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq503649
       have r₂ := eq418979
       grind)
    | exact resolve eq503649 eq418979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503649
  have eq503652 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq503650 eq21
    | exact resolve eq21 eq503650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503756 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq503650 eq1004
    | exact resolve eq1004 eq503650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq504584 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq503652
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq503652
    | exact resolve eq503652 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503652
  have eq507626 : x = (k x x) ∨ x = y := by grind
  clear eq503756
  have eq510465 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq507626
       grind)
    | exact superpose eq507626 eq44
    | exact resolve eq44 eq507626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq507626
  have eq510620 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq510465
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq510465
    | exact resolve eq510465 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510465
  have eq511176 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq504584 eq510620
    | exact resolve eq510620 eq504584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504584 eq510620
  have eq511317 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq511176
  have eq516183 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq511317 eq158
    | exact resolve eq158 eq511317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq511317
  have eq516275 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq31 eq516183
    | exact resolve eq516183 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq516183
  have eq516497 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq516275 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq516275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516275
  have eq516519 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq516497
  have eq516631 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq516519 eq209
    | exact resolve eq209 eq516519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq516519
  have eq516920 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq503650 eq516631
    | exact resolve eq516631 eq503650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516631
  have eq517095 : y = (M.op x y) ∨ x = y := by grind
  clear eq516920
  have eq517097 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq517095
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq517095
    | exact resolve eq517095 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517095
  have eq520105 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq517097 eq503650
    | exact resolve eq503650 eq517097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503650 eq517097
  have eq520114 : x = y := by grind
  clear eq520105
  have eq520361 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq520114
       grind)
    | exact superpose eq520114 eq19
    | exact resolve eq19 eq520114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq520362 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq520114
       grind)
    | exact superpose eq520114 eq25
    | exact resolve eq25 eq520114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq520601 : x = (M.op x x) ∨ x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32048
       have i₂ := eq520114
       grind)
    | exact superpose eq520114 eq32048
    | exact resolve eq32048 eq520114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32048 eq520114
  have eq520786 : x = (M.op x x) ∨ x = (k x x) := by grind
  clear eq520601
  have eq520806 : x = (M.op x x) := by
    first
    | (have j1 := eq3791 x
       grind)
    | (have r₁ := eq520786
       have r₂ := eq3791 x
       grind)
    | exact resolve eq520786 eq3791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3791 eq520786
  have eq520958 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq520362
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq520362
    | exact resolve eq520362 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520362
  have eq521295 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq520958 eq418979
    | exact resolve eq418979 eq520958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418979 eq520958
  have eq522157 : x = (M.op x y) := by
    first
    | (have i₁ := eq520806
       have i₂ := eq520361
       grind)
    | exact superpose eq520361 eq520806
    | exact resolve eq520806 eq520361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520361 eq520806
  have eq522160 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq522157 eq21
    | exact resolve eq21 eq522157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq522157
  have eq523265 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq522160
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq522160
    | exact resolve eq522160 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq522160
  have eq523608 : False := by grind
  exact eq523608

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq175 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 y
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq185 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq190 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq187 eq16
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq182 eq185
    | exact resolve eq185 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq555 : y = (k (M.op y y) y) := by
    first
    | (have i₁ := eq551
       have i₂ := eq181 y
       grind)
    | exact superpose eq181 eq551
    | exact resolve eq551 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq556 : (σ y) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq41 (M.op y y)
       have i₂ := eq555
       grind)
    | exact superpose eq555 eq41
    | exact resolve eq41 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : (σ y) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq556
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq556
    | exact resolve eq556 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq570 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq187 eq190
    | exact resolve eq190 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq190
  have eq574 : (σ y) = (k (M.op (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq570
       have i₂ := eq181 sF3
       grind)
    | exact superpose eq181 eq570
    | exact resolve eq570 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq633 : (M.op x y) = (k x y) ∨ y = (M.op y x) := by
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
  have eq646 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq678 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq633
       grind)
    | exact superpose eq633 eq41
    | exact resolve eq41 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq633
  have eq679 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq678
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq678
    | exact resolve eq678 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq681 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq679
    | exact resolve eq679 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq691 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq681 eq646
    | exact resolve eq646 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq698 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq691
       have r₂ := eq27
       grind)
    | exact resolve eq691 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq703 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq698 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq698
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq698
       grind)
    | exact resolve eq12 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq698 eq16
    | exact resolve eq16 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq703
  have eq709 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq681 eq707
    | exact resolve eq707 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq725 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq709 eq181
    | exact resolve eq181 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq727 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq725
    | exact resolve eq725 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq681 eq727
    | exact resolve eq727 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq727
  have eq732 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq730
       have r₂ := eq27
       grind)
    | exact resolve eq730 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq736 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq732
       grind)
    | exact superpose eq732 eq16
    | exact resolve eq16 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : x = (M.op (M.op y y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq736 x
       have i₂ := eq732
       grind)
    | exact superpose eq732 eq736
    | exact resolve eq736 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq764 : y = (M.op (k (M.op y y) y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq736 y
       have i₂ := eq181 y
       grind)
    | exact superpose eq181 eq736
    | exact resolve eq736 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq773 : x = (M.op (M.op y y) x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq762
  have eq775 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq764
       have i₂ := eq555
       grind)
    | exact superpose eq555 eq764
    | exact resolve eq764 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq764
  have eq820 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) x) X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) x
       have i₂ := eq773
       grind)
    | exact superpose eq773 eq16
    | exact resolve eq16 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq824 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq775 eq820
    | exact resolve eq820 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq820
  have eq1345 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq824 y
       have i₂ := eq773
       grind)
    | exact superpose eq773 eq824
    | exact resolve eq824 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq824
  have eq1352 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1345
  have eq1364 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1352
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1352
    | exact resolve eq1352 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq1378 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1364 eq29
    | exact resolve eq29 eq1364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1364
  have eq1397 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq1378
    | exact resolve eq1378 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1378
  have eq1398 : y = (M.op x y) := by grind
  clear eq1397
  have eq1408 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1398
       grind)
    | exact superpose eq1398 eq18
    | exact resolve eq18 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1409 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1398
       grind)
    | exact superpose eq1398 eq24
    | exact resolve eq24 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1414 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq185 X0
       have i₂ := eq1398
       grind)
    | exact superpose eq1398 eq185
    | exact resolve eq185 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq1418 : (σ y) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq557
       have i₂ := eq1398
       grind)
    | exact superpose eq1398 eq557
    | exact resolve eq557 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq1439 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1409 eq20
    | exact resolve eq20 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1442 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq1409 eq15
    | exact resolve eq15 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2242 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1414 (M.op sF0 x)
       have i₂ := eq16 sF0 sF0 x
       grind)
    | exact superpose eq16 eq1414
    | exact resolve eq1414 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq3134 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq698 eq705
    | exact resolve eq705 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3139 : (σ y) = (M.op (k (M.op (σ y) (σ y)) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq705 sF3
       have i₂ := eq181 sF3
       grind)
    | exact superpose eq181 eq705
    | exact resolve eq705 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq705
  have eq3156 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq3134
  have eq3171 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq574 eq3139
    | exact resolve eq3139 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq3139
  have eq3173 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3156
       have i₂ := eq1398
       grind)
    | exact superpose eq1398 eq3156
    | exact resolve eq3156 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq3176 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3171
       have i₂ := eq1398
       grind)
    | exact superpose eq1398 eq3171
    | exact resolve eq3171 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3171
  have eq3300 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq3176 eq3173
    | exact resolve eq3173 eq3176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173 eq3176
  have eq3315 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq3300
  have eq3768 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq3315 eq698
    | exact resolve eq698 eq3315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq3315
  have eq3791 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3768
       have i₂ := eq1398
       grind)
    | exact superpose eq1398 eq3768
    | exact resolve eq3768 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398 eq3768
  have eq3792 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by grind
  clear eq3791
  have eq3806 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3792 eq2242
    | exact resolve eq2242 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3808 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq3792 eq16
    | exact resolve eq16 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3829 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2242 eq3808
    | exact resolve eq3808 eq2242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242 eq3808
  have eq3987 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3806 eq3829
    | exact resolve eq3829 eq3806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3806 eq3829
  have eq4014 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by grind
  clear eq3987
  have eq4020 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3792 eq4014
    | exact resolve eq4014 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3792 eq4014
  have eq4185 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4020 eq1442
    | exact resolve eq1442 eq4020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442 eq4020
  have eq4200 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq4185
    | exact resolve eq4185 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4185
  have eq4201 : x = (M.op x y) := by grind
  clear eq4200
  have eq4234 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4201
       grind)
    | exact superpose eq4201 eq22
    | exact resolve eq22 eq4201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4263 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1408
       have i₂ := eq4201
       grind)
    | exact superpose eq4201 eq1408
    | exact resolve eq1408 eq4201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408 eq4201
  have eq4293 : (σ x) = (σ y) := by
    first
    | exact superpose eq4234 eq1409
    | exact resolve eq1409 eq4234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq4294 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4234 eq20
    | exact resolve eq20 eq4234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4234
  have eq4320 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4293 eq26
    | exact resolve eq26 eq4293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4354 : (σ x) = (k (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
    first
    | exact superpose eq4293 eq1418
    | exact resolve eq1418 eq4293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq4373 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq4263 eq4354
    | exact resolve eq4354 eq4263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4263 eq4354
  have eq4391 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq4373
    | exact resolve eq4373 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4373
  have eq4406 : (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1439 eq4391
    | exact resolve eq4391 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439 eq4391
  have eq4410 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4293 eq4406
    | exact resolve eq4406 eq4293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4293 eq4406
  have eq4553 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4320 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq4320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4320
  have eq4566 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4410 eq4553
    | exact resolve eq4553 eq4410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4410 eq4553
  have eq4567 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4566
  have eq4568 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4567 eq27
    | exact resolve eq27 eq4567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4567
  have eq4587 : False := by grind
  exact eq4587

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
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
  clear eq45
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq82
    | exact resolve eq82 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq90
    | exact resolve eq90 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq149 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq132
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq132
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq132 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq156 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq149
  have eq380 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq380 (M.op X0 X1)
       grind)
    | exact superpose eq380 eq53
    | exact resolve eq53 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq380 X0
       grind)
    | exact superpose eq380 eq14
    | exact resolve eq14 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) X5)) X1) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X0 X5
       have i₂ := eq56 X3 X2 X4 X0
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq56
  have eq698 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq75 X0 X0
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq380 (σ X0)
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq380
    | (have j1 := eq75 X0 X0
       grind)
    | exact resolve eq380 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq713 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq706 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq715 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq698 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq698
    | (have j0 := eq698 X0 X1
       grind)
    | exact resolve eq698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq967 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq388
    | exact resolve eq388 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11029 : (M.op (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq156 eq16
    | exact resolve eq16 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq11076 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq155 eq11029
    | exact resolve eq11029 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11029
  have eq11254 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) (M.op X0 X4)) (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq459 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X1 X0 X2 X4
       have i₂ := eq14 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq14 eq459
    | exact resolve eq459 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq11290 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op X0 X3) (M.op X0 X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq11254 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq11254
    | exact resolve eq11254 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11254
  have eq29863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq29863
    | exact resolve eq29863 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29863
  have eq29884 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq29873
       have r₂ := eq28
       grind)
    | exact resolve eq29873 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29873
  have eq29886 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29884 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq29884
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq29884
       grind)
    | exact resolve eq12 eq29884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29933 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29884 eq967
    | exact resolve eq967 eq29884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29884
  have eq29936 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq29886
  have eq29937 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq29936
  have eq30030 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  have eq30292 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29937 eq91
    | exact resolve eq91 eq29937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29937
  have eq30310 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq30292
  have eq30316 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29933 eq30310
    | exact resolve eq30310 eq29933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29933
  have eq30320 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq30310 eq380
    | exact resolve eq380 eq30310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30310
  have eq30373 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq30316
  have eq30376 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq30320
    | exact resolve eq30320 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30320
  have eq30378 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq30373
       have r₂ := eq30030
       grind)
    | exact resolve eq30373 eq30030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30030 eq30373
  have eq30495 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30376 eq967
    | exact resolve eq967 eq30376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30509 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq30378
  have eq30564 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq30509
    | exact resolve eq30509 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30509
  have eq31250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30564 eq91
    | exact resolve eq91 eq30564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq30564
  have eq31269 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq31250
  have eq31272 : y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq31269
       have r₂ := eq28
       grind)
    | exact resolve eq31269 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31269
  have eq31275 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq31272
       grind)
    | exact superpose eq31272 eq14
    | exact resolve eq14 eq31272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31321 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq967 y x
       have i₂ := eq31272
       grind)
    | exact superpose eq31272 eq967
    | exact resolve eq967 eq31272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31350 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq31275 X0
       have i₂ := eq967 y X0
       grind)
    | exact superpose eq967 eq31275
    | exact resolve eq31275 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31275
  have eq31494 : x ≠ y ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq31321
  have eq31847 : x = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq31350 x
       have i₂ := eq31272
       grind)
    | exact superpose eq31272 eq31350
    | exact resolve eq31350 eq31272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31350
  have eq31937 : x = (M.op y y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq31847
  have eq32015 : x = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq967 y y
       have i₂ := eq31937
       grind)
    | exact superpose eq31937 eq967
    | exact resolve eq967 eq31937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31937
  have eq32018 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq32015
  have eq32028 : x = y ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq31272
       have i₂ := eq32018
       grind)
    | exact superpose eq32018 eq31272
    | exact resolve eq31272 eq32018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31272 eq32018
  have eq32083 : x = y ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq32028
  have eq32088 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq32083
       have r₂ := eq31494
       grind)
    | exact resolve eq32083 eq31494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31494 eq32083
  have eq32219 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq380 y
       have i₂ := eq32088
       grind)
    | exact superpose eq32088 eq380
    | exact resolve eq380 eq32088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq32088
  have eq32279 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32219
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32219
    | exact resolve eq32219 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32219
  have eq32283 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32279 eq30
    | exact resolve eq30 eq32279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32279
  have eq32443 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq32283
    | exact resolve eq32283 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32283
  have eq32444 : y = (M.op x y) := by grind
  clear eq32443
  have eq32445 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32444 eq21
    | exact resolve eq21 eq32444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32611 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq32445
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32445
    | exact resolve eq32445 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32445
  have eq32613 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq32611 eq27
    | exact resolve eq27 eq32611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32711 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32611 eq30495
    | exact resolve eq30495 eq32611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30495
  have eq32712 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq32711
       have r₂ := eq28
       grind)
    | exact resolve eq32711 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32711
  have eq37327 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ y) X0)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30376 eq11290
    | exact resolve eq11290 eq30376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30376
  have eq37417 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32611 eq37327
    | exact resolve eq37327 eq32611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37327
  have eq37519 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37417 x
       have i₂ := eq967 sF1 x
       grind)
    | exact superpose eq967 eq37417
    | exact resolve eq37417 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37417
  have eq37536 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq32611 eq37519
    | (have j0 := eq37519 X0
       grind)
    | exact resolve eq37519 eq32611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37519
  have eq37545 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq37536 X0
       grind)
    | (have r₁ := eq37536 X0
       have r₂ := eq28
       grind)
    | exact resolve eq37536 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37536
  have eq39704 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  have eq39708 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq32712 eq388
    | exact resolve eq388 eq32712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41852 : (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11076 eq713
    | (have j0 := eq713 (M.op x y)
       grind)
    | exact resolve eq713 eq11076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq11076
  have eq42107 : (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21 eq41852
    | exact resolve eq41852 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41852
  have eq42171 : (σ (M.op x y)) = (M.op (σ (M.op y y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq32444 eq42107
    | exact resolve eq42107 eq32444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42107
  have eq42207 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op y y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21 eq42171
    | exact resolve eq42171 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq42171
  have eq42213 : (σ (M.op x y)) = (M.op (σ (M.op y y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32444 eq42207
    | exact resolve eq42207 eq32444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42207
  have eq53161 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq39704 eq155
    | exact resolve eq155 eq39704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq39704
  have eq53211 : (k y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32444 eq53161
    | exact resolve eq53161 eq32444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53161
  have eq95639 : (τ (σ (M.op x y))) = (k y y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32712 eq53211
    | exact resolve eq53211 eq32712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32712 eq53211
  have eq95746 : (τ (σ (M.op x y))) = (k y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq95639
  have eq95781 : (M.op x y) = (k y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq95746
    | exact resolve eq95746 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq95746
  have eq95794 : y = (k y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32444 eq95781
    | exact resolve eq95781 eq32444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95781
  have eq95849 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq95794
       grind)
    | exact superpose eq95794 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq95794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95794
  have eq95869 : y = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq95849
  have eq96040 : x ≠ y ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq95869
  have eq171264 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq37545 eq39708
    | exact resolve eq39708 eq37545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37545 eq39708
  have eq171394 : ∀ X0 : G, y = (M.op y x) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq171264 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171264
  have eq171543 : ∀ X0 : G, x = (M.op (M.op x y) x) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq384 y x
       have i₂ := eq171394 X0
       grind)
    | exact superpose eq171394 eq384
    | (have j1 := eq171394 X0
       grind)
    | exact resolve eq384 eq171394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq171569 : ∀ X0 : G, y = (M.op y y) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq967 y x
       have i₂ := eq171394 X0
       grind)
    | exact superpose eq171394 eq967
    | (have j1 := eq171394 X0
       grind)
    | exact resolve eq967 eq171394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171602 : ∀ X0 : G, x = (M.op (M.op x y) x) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq171543 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq171543
    | (have j0 := eq171543 X0
       grind)
    | exact resolve eq171543 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq171543
  have eq171635 : ∀ X0 : G, x = (M.op y y) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq32444 eq171602
    | (have j0 := eq171602 X0
       grind)
    | exact resolve eq171602 eq32444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32444 eq171602
  have eq171822 : ∀ X0 : G, x ≠ y ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq171569 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171569
  have eq172609 : ∀ X0 : G, x = (M.op y x) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq967 y y
       have i₂ := eq171635 X0
       grind)
    | exact superpose eq171635 eq967
    | (have j1 := eq171635 X0
       grind)
    | exact resolve eq967 eq171635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171635
  have eq172620 : ∀ X0 : G, x = (M.op y x) ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq172609 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172609
  have eq172662 : ∀ X0 X1 : G, x = y ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op y y) ∨ (M.op (σ (M.op x y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq171394 X0
       have i₂ := eq172620 X1
       grind)
    | exact superpose eq172620 eq171394
    | (have j0 := eq171394 X0
       have j1 := eq172620 X0
       grind)
    | exact resolve eq171394 eq172620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171394 eq172620
  have eq172740 : ∀ X0 X1 : G, x = (M.op y y) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op (σ (M.op x y)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq172662 X0 X0
       have j1 := eq171822 X0
       grind)
    | (have r₁ := eq172662 X0 X1
       have r₂ := eq171822 X0
       grind)
    | exact resolve eq172662 eq171822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171822 eq172662
  have eq173068 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op (σ (M.op x y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42213
       have i₂ := eq172740 X0 X1
       grind)
    | exact superpose eq172740 eq42213
    | (have j1 := eq172740 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq42213 eq172740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42213 eq172740
  have eq173183 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op (σ (M.op x y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq173068 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq173068
    | (have j0 := eq173068 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq173068 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173068
  have eq173198 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op (σ (M.op x y)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq32613 eq173183
    | (have j0 := eq173183 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq173183 eq32613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173183
  have eq173201 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op (σ (M.op x y)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq173198 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq173198 X0 X1
       have r₂ := eq28
       grind)
    | exact resolve eq173198 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173198
  have eq181090 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq173201 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173201
  have eq181091 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq181090 (σ (M.op x y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181090
  have eq181215 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have j0 := eq181091 (σ (M.op x y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181091
  have eq181216 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq181215
  have eq181359 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq181216 eq388
    | exact resolve eq388 eq181216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq181428 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq181216 eq11290
    | exact resolve eq11290 eq181216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11290 eq181216
  have eq181430 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq181428 x
       have i₂ := eq967 sF1 x
       grind)
    | exact superpose eq967 eq181428
    | exact resolve eq181428 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq181428
  have eq187431 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq181430 eq181359
    | exact resolve eq181359 eq181430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181359
  have eq187575 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq187431 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187431
  have eq187702 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq187575 eq181430
    | exact resolve eq181430 eq187575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181430 eq187575
  have eq187931 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq187702 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187702
  have eq188727 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq187931 eq32613
    | exact resolve eq32613 eq187931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187931
  have eq188795 : x = y := by
    first
    | (have r₁ := eq188727
       have r₂ := eq28
       grind)
    | exact resolve eq188727 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188727
  have eq188867 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq188795
       grind)
    | exact superpose eq188795 eq25
    | exact resolve eq25 eq188795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq189076 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq96040
       have i₂ := eq188795
       grind)
    | exact superpose eq188795 eq96040
    | (have r₁ := eq96040
       have r₂ := eq188795
       grind)
    | exact resolve eq96040 eq188795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96040 eq188795
  have eq189178 : x ≠ x ∨ x = (M.op x x) := by grind
  clear eq189076
  have eq189179 : x = (M.op x x) := by grind
  clear eq189178
  have eq189342 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq32611 eq188867
    | exact resolve eq188867 eq32611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32611 eq188867
  have eq189427 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq189342
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq189342
    | exact resolve eq189342 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189342
  have eq189569 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq189427 eq32613
    | exact resolve eq32613 eq189427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32613
  have eq189872 : (k x x) = (M.op x x) := by grind
  have eq189977 : x = (k x x) := by
    first
    | (have i₁ := eq189872
       have i₂ := eq189179
       grind)
    | exact superpose eq189179 eq189872
    | exact resolve eq189872 eq189179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189179 eq189872
  have eq192490 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq715 x x
       have i₂ := eq189977
       grind)
    | exact superpose eq189977 eq715
    | (have j0 := eq715 x x
       grind)
    | exact resolve eq715 eq189977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715 eq189977
  have eq192497 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq192490
  have eq192498 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq192497
  have eq192515 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq192498
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq192498
    | exact resolve eq192498 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq192498
  have eq192540 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq189427 eq192515
    | exact resolve eq192515 eq189427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189427 eq192515
  have eq192565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq189569 eq192540
    | exact resolve eq192540 eq189569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189569 eq192540
  have eq192589 : False := by grind
  exact eq192589
