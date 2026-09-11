import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_y_pyy_pyx_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
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
  clear eq22
  have eq456 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq2775 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq456 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq456 X0 X1
       grind)
    | exact superpose eq456 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq456 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq456 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq456 X0 X0
       grind)
    | exact resolve eq13 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2796 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq456 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq2798 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2775 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775
  have eq2802 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2798 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2798
    | (have j0 := eq2798 X0 X1
       grind)
    | exact resolve eq2798 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2798
  have eq2811 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2802 X0 X1
       have j1 := eq2796 X0 X1
       grind)
    | (have r₁ := eq2802 X0 X1
       have r₂ := eq2796 X0 (k X1 X0)
       grind)
    | (have r₁ := eq2802 X0 X1
       have r₂ := eq2796 X0 X1
       grind)
    | (have r₁ := eq2802 X0 X0
       have r₂ := eq2796 X0 (k X0 X0)
       grind)
    | exact resolve eq2802 eq2796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2796 eq2802
  have eq35142 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2811 (τ X0) (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq2811
    | (have j0 := eq2811 (τ X1) (τ X0)
       grind)
    | exact resolve eq2811 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2811
  have eq35307 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35142 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35142
    | (have j0 := eq35142 X0 X1
       grind)
    | exact resolve eq35142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35142
  have eq35348 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35307 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq35307
    | (have j0 := eq35307 X0 X1
       grind)
    | exact resolve eq35307 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35307
  have eq35386 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35348 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq35348
    | (have j0 := eq35348 X0 X1
       grind)
    | exact resolve eq35348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35348
  have eq35418 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (M.op X1 X0) = (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35386 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35386
    | (have j0 := eq35386 X0 X1
       grind)
    | exact resolve eq35386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35386
  have eq35443 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35418 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq35418
    | (have j0 := eq35418 X0 X1
       grind)
    | exact resolve eq35418 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35418
  have eq35464 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35443 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35443
    | (have j0 := eq35443 X0 X1
       grind)
    | exact resolve eq35443 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35443
  have eq35481 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35464 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq35464
    | (have j0 := eq35464 X0 X1
       grind)
    | exact resolve eq35464 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35464
  have eq36140 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35481 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35481
  have eq36146 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq36140 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq36140 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq36140 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq36140 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq36140 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36140
  have eq36381 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36146 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq36146
    | (have j0 := eq36146 (σ X0) (σ X1)
       grind)
    | exact resolve eq36146 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39824 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36146 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq36146 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36146 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40291 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39824 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq39824
    | exact resolve eq39824 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40498 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39824 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46967 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40291 X0 X1
       have i₂ := eq39824 X0 X1
       grind)
    | exact superpose eq39824 eq40291
    | (have j1 := eq39824 X1 X0
       grind)
    | exact resolve eq40291 eq39824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39824 eq40291
  have eq70634 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46967 x y
       grind)
    | exact superpose eq46967 eq16
    | (have j1 := eq46967 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq46967 x y
       grind)
    | exact resolve eq16 eq46967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46967
  have eq70884 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by grind
  clear eq70634
  have eq70986 : (M.op x y) = (τ (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq70884
       grind)
    | exact superpose eq70884 eq10
    | exact resolve eq10 eq70884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70884
  have eq71159 : x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq70986
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq70986
    | exact resolve eq70986 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70986
  have eq71161 : x = (k y x) := by
    first
    | (have j1 := eq40498 y x
       grind)
    | (have r₁ := eq71159
       have r₂ := eq40498 y x
       grind)
    | exact resolve eq71159 eq40498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40498 eq71159
  have eq71163 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71161
       have i₂ := eq36146 y x
       grind)
    | exact superpose eq36146 eq71161
    | (have j1 := eq36146 y x
       grind)
    | exact resolve eq71161 eq36146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36146
  have eq71165 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36381 y x
       have i₂ := eq71161
       grind)
    | exact superpose eq71161 eq36381
    | (have j0 := eq36381 y x
       grind)
    | exact resolve eq36381 eq71161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36381 eq71161
  have eq71172 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq71163
       grind)
    | exact superpose eq71163 eq9
    | exact resolve eq9 eq71163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71305 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq71312 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq71172 y
       grind)
    | exact superpose eq71172 eq9
    | exact resolve eq9 eq71172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71172
  have eq71813 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq71312 eq71163
    | (have j1 := eq71312 x
       grind)
    | exact resolve eq71163 eq71312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71163 eq71312
  have eq71952 : x = (M.op x y) := by
    first
    | (have r₁ := eq71813
       have r₂ := eq71305
       grind)
    | exact resolve eq71813 eq71305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71305 eq71813
  have eq71954 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq71952
       grind)
    | exact superpose eq71952 eq16
    | exact resolve eq16 eq71952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71952
  have eq89843 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq71165
       have r₂ := eq71954
       grind)
    | exact resolve eq71165 eq71954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71165
  have eq89844 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq71954
       have i₂ := eq89843
       grind)
    | exact superpose eq89843 eq71954
    | exact resolve eq71954 eq89843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71954
  have eq89851 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq89843
       grind)
    | exact superpose eq89843 eq9
    | exact resolve eq9 eq89843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90015 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq89851 (σ y)
       grind)
    | exact superpose eq89851 eq9
    | exact resolve eq9 eq89851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89851
  have eq91065 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq89843
       have i₂ := eq90015 (σ x)
       grind)
    | exact superpose eq90015 eq89843
    | exact resolve eq89843 eq90015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89843 eq90015
  have eq91332 : False := by grind
  exact eq91332

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pxy_y_pxy_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq18
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op X1 (M.op X1 (M.op X2 X1))) X0) = (M.op (M.op X1 (M.op X1 (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X1 (M.op X2 X1))) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 (M.op X1 (M.op X2 X1))) X0
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op X1 (M.op X2 X1))) X0
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 (M.op X2 X1))) X0) = (M.op (M.op X1 (M.op X1 (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq275 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq283 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq282 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq290 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq283 X0 X1
       grind)
    | exact superpose eq283 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq283 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq283 X0 X1
       grind)
    | exact resolve eq13 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq283 X1 X0
       grind)
    | exact superpose eq283 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq283 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq283 X1 X1
       grind)
    | exact resolve eq12 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X2
       have i₂ := eq283 X2 X0
       grind)
    | exact superpose eq283 eq9
    | (have j1 := eq283 X2 X0
       grind)
    | exact resolve eq9 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 (M.op X0 X1))) = X2 ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X0
       have i₂ := eq283 X1 (M.op X0 X1)
       grind)
    | exact superpose eq283 eq9
    | (have j1 := eq283 X1 (M.op X0 X1)
       grind)
    | exact resolve eq9 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq291 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq300 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq290 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq302 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq300 X0 X1
       have j1 := eq299 X0 X1
       grind)
    | (have r₁ := eq300 X0 X1
       have r₂ := eq299 X0 X1
       grind)
    | (have r₁ := eq300 X1 X0
       have r₂ := eq299 X0 X1
       grind)
    | (have r₁ := eq300 X0 X1
       have r₂ := eq299 (k X0 X1) X1
       grind)
    | exact resolve eq300 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq306 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq299 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq317 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq306 (σ X0)
       grind)
    | exact superpose eq306 eq15
    | exact resolve eq15 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq317 X0
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq317
    | exact resolve eq317 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq317
  have eq430 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq302 (σ X0) X1
       grind)
    | exact superpose eq302 eq28
    | (have j1 := eq302 (σ X0) X1
       grind)
    | exact resolve eq28 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq439 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq302 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq448 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq439 X1 X0
       have i₂ := eq283 X1 X0
       grind)
    | exact superpose eq283 eq439
    | (have j0 := eq439 X1 X0
       have j1 := eq283 X1 X0
       grind)
    | (have r₁ := eq439 X0 X1
       have r₂ := eq283 X0 X1
       grind)
    | exact resolve eq439 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq452 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq448 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq1470 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq430 X1 (σ X0)
       grind)
    | exact superpose eq430 eq22
    | (have j1 := eq430 X1 (σ X0)
       grind)
    | exact resolve eq22 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq430
  have eq1477 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1470 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1470
    | (have j0 := eq1470 X0 X1
       grind)
    | exact resolve eq1470 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1495 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1477 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1477
    | (have j0 := eq1477 X0 X1
       grind)
    | exact resolve eq1477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq1504 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1495 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1495
    | (have j0 := eq1495 X0 X1
       grind)
    | exact resolve eq1495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495
  have eq1569 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq1504 X1 X0
       grind)
    | exact superpose eq1504 eq11
    | (have j1 := eq1504 X1 X0
       grind)
    | exact resolve eq11 eq1504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq1596 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1569 X0 X1
       have i₂ := eq452 X0 X1
       grind)
    | exact superpose eq452 eq1569
    | (have j0 := eq1569 X1 X0
       have j1 := eq452 X0 X1
       grind)
    | exact resolve eq1569 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq1569
  have eq29489 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = X2 ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq294 X0 X1 X2
       have i₂ := eq283 X1 (M.op X0 X1)
       grind)
    | exact superpose eq283 eq294
    | (have j0 := eq294 X0 X1 X2
       have j1 := eq283 X1 (M.op X0 X1)
       grind)
    | exact resolve eq294 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq294
  have eq29610 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) ∨ (M.op X2 (M.op X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq29489 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29489
  have eq30558 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = (k X0 (M.op X1 (M.op X1 (M.op X2 X1)))) ∨ (M.op X3 X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29610 X0 (M.op X1 (M.op X1 (M.op X2 X1))) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq29610
    | exact resolve eq29610 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29610
  have eq30769 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 ∨ (M.op X3 X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30558 X0 X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq30558
    | (have j0 := eq30558 X0 X1 X2 X3
       grind)
    | exact resolve eq30558 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30558
  have eq158000 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1596 x y
       grind)
    | exact superpose eq1596 eq16
    | (have j1 := eq1596 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1596 x y
       grind)
    | exact resolve eq16 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq158198 : y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq158000
  have eq158369 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq158198
       grind)
    | exact superpose eq158198 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq158198
       grind)
    | exact resolve eq13 eq158198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158198
  have eq158433 : y ≠ y ∨ x = y ∨ x = (k y x) := by grind
  clear eq158369
  have eq158434 : x = y ∨ x = (k y x) := by grind
  clear eq158433
  have eq158436 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq158434
       grind)
    | exact superpose eq158434 eq16
    | exact resolve eq16 eq158434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158434
  have eq158450 : x = (k y x) := by
    first
    | (have r₁ := eq158436
       have r₂ := eq336 x
       grind)
    | exact resolve eq158436 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158436
  have eq158479 : ∀ X0 : G, x = (M.op y x) ∨ (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq292 y X0 x
       have i₂ := eq158450
       grind)
    | exact superpose eq158450 eq292
    | (have j0 := eq292 y X0 x
       grind)
    | exact resolve eq292 eq158450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq159340 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op y y))) = X1 ∨ (M.op X0 (M.op x (M.op x x))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq158479 X1
       grind)
    | exact superpose eq158479 eq9
    | (have j1 := eq158479 X1
       grind)
    | exact resolve eq9 eq158479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158479
  have eq168358 : ∀ X0 X1 : G, (M.op X1 (M.op x (M.op x x))) = X1 ∨ (k y X0) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 y y
       have i₂ := eq159340 X0 y
       grind)
    | exact superpose eq159340 eq64
    | (have j1 := eq159340 X1 X1
       grind)
    | exact resolve eq64 eq159340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq159340
  have eq169594 : ∀ X0 X1 : G, (M.op X0 x) = X0 ∨ (k y X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq168358 X1 x
       grind)
    | exact superpose eq168358 eq9
    | (have j1 := eq168358 X1 X1
       grind)
    | exact resolve eq9 eq168358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169623 : ∀ X0 X1 X2 : G, (k y X2) = (M.op y X2) ∨ (M.op X1 X0) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30769 X0 x x X1
       have i₂ := eq168358 X2 x
       grind)
    | exact superpose eq168358 eq30769
    | (have j0 := eq30769 X0 X1 X2 X1
       have j1 := eq168358 X2 X1
       grind)
    | exact resolve eq30769 eq168358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30769 eq168358
  have eq181147 : ∀ X0 : G, y ≠ (M.op y x) ∨ (M.op X0 y) = X0 ∨ y = (k y x) := by
    intro X0
    first
    | (have j0 := eq169623 y X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169623
  have eq181148 : ∀ X0 : G, y ≠ (M.op y x) ∨ x = y ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq181147 X0
       have i₂ := eq158450
       grind)
    | exact superpose eq158450 eq181147
    | (have j0 := eq181147 X0
       grind)
    | exact resolve eq181147 eq158450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181147
  have eq181165 : ∀ X0 X1 : G, y ≠ y ∨ x = y ∨ (M.op X0 y) = X0 ∨ (k y X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq181148 X0
       have i₂ := eq169594 y X1
       grind)
    | exact superpose eq169594 eq181148
    | (have j0 := eq181148 X0
       have j1 := eq169594 X0 X1
       grind)
    | (have r₁ := eq181148 X0
       have r₂ := eq169594 y X1
       grind)
    | exact resolve eq181148 eq169594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169594 eq181148
  have eq181169 : ∀ X0 X1 : G, x = y ∨ (M.op X0 y) = X0 ∨ (k y X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have j0 := eq181165 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181165
  have eq181254 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op X0 y) = X0 ∨ (k y X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq181169 X0 X1
       grind)
    | exact superpose eq181169 eq16
    | (have j1 := eq181169 X0 X1
       grind)
    | exact resolve eq16 eq181169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181169
  have eq181363 : ∀ X0 X1 : G, (M.op X0 y) = X0 ∨ (k y X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have j0 := eq181254 X0 X1
       grind)
    | (have r₁ := eq181254 X0 X1
       have r₂ := eq336 x
       grind)
    | exact resolve eq181254 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181254
  have eq181431 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k y X0) = (M.op y X0) ∨ (k y X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq181363 X0 X1
       grind)
    | exact superpose eq181363 eq12
    | (have j0 := eq12 y X0
       have j1 := eq181363 X0 X0
       grind)
    | (have r₁ := eq12 y X0
       have r₂ := eq181363 X0 X1
       grind)
    | exact resolve eq12 eq181363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181363
  have eq181535 : ∀ X0 X1 : G, (k y X0) = (M.op y X0) ∨ (k y X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have j0 := eq181431 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181431
  have eq181853 : ∀ X0 : G, (M.op y X0) ≠ (M.op y X0) ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq181535 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181535
  have eq181854 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq181853 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181853
  have eq181951 : x = (M.op y x) := by
    first
    | (have i₁ := eq158450
       have i₂ := eq181854 x
       grind)
    | exact superpose eq181854 eq158450
    | exact resolve eq158450 eq181854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158450 eq181854
  have eq182131 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq181951
       grind)
    | exact superpose eq181951 eq9
    | exact resolve eq9 eq181951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182215 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq182131 x
       grind)
    | exact superpose eq182131 eq9
    | exact resolve eq9 eq182131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182131
  have eq182782 : x = y := by
    first
    | (have i₁ := eq181951
       have i₂ := eq182215 y
       grind)
    | exact superpose eq182215 eq181951
    | exact resolve eq181951 eq182215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181951 eq182215
  have eq182895 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq182782
       grind)
    | exact superpose eq182782 eq16
    | exact resolve eq16 eq182782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182782
  have eq183009 : False := by grind
  exact eq183009

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_y_pxy_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op X2 (M.op X3 X2))) (M.op (M.op X2 (M.op X2 (M.op X3 X2))) X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X2 (M.op X2 (M.op X3 X2))) X0
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) ≠ (M.op X0 (M.op X0 (M.op X1 X0))) ∨ (k X2 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op X2 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op X0 (M.op X1 X0)))
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X1 (M.op X2 X1)))
       have r₂ := eq9 (M.op X1 (M.op X1 (M.op X2 X1))) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op X2 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X0 (M.op X1 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq69 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X1 (M.op X2 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (M.op X1 (M.op X1 (M.op X2 X1)))
       have i₂ := eq35 X1 X2 (σ X0)
       grind)
    | exact superpose eq35 eq30
    | exact resolve eq30 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X1 (M.op X2 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op X1 (M.op X1 (M.op X2 X1)))
       have i₂ := eq35 X1 X2 (τ X0)
       grind)
    | exact superpose eq35 eq17
    | exact resolve eq17 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X1 (M.op X2 X1))))) = X0 := by
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
  have eq72 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X1 (M.op X2 X1))))) = X0 := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq99 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 (M.op X1 (M.op X2 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (τ (M.op X1 (M.op X1 (M.op X2 X1))))
       have i₂ := eq72 (σ X0) X1 X2
       grind)
    | exact superpose eq72 eq30
    | exact resolve eq30 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op X1 (M.op X1 (M.op X2 X1)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99
    | exact resolve eq99 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq143 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (τ (τ (M.op X1 (M.op X1 (M.op X2 X1)))))
       have i₂ := eq105 (σ X0) X1 X2
       grind)
    | exact superpose eq105 eq30
    | exact resolve eq30 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq143 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq143
    | exact resolve eq143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq217 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1)))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1))))))
       have i₂ := eq149 (σ X0) X1 X2
       grind)
    | exact superpose eq149 eq30
    | exact resolve eq30 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq223 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq217 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq217
    | exact resolve eq217 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq296 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 X0 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq76
    | exact resolve eq76 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq76 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq76 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq315 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq310 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq316 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq315 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq315 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq315 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq487 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 (M.op X1 X0)))) ≠ (σ (M.op X0 (M.op X0 (M.op X1 X0)))) ∨ (k X2 (σ (M.op X0 (M.op X0 (M.op X1 X0))))) = (M.op X2 (σ (M.op X0 (M.op X0 (M.op X1 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq316 (M.op X0 (M.op X0 (M.op X1 X0))) X2
       have i₂ := eq35 X0 X1 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq35 eq316
    | (have j0 := eq316 (M.op X0 (M.op X0 (M.op X1 X0))) X2
       grind)
    | exact resolve eq316 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq493 : ∀ X0 X1 X2 : G, (σ (τ (τ (M.op X0 (M.op X0 (M.op X1 X0)))))) ≠ (σ (τ (τ (M.op X0 (M.op X0 (M.op X1 X0)))))) ∨ (k X2 (σ (τ (τ (M.op X0 (M.op X0 (M.op X1 X0))))))) = (M.op X2 (σ (τ (τ (M.op X0 (M.op X0 (M.op X1 X0))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq316 (τ (τ (M.op X0 (M.op X0 (M.op X1 X0))))) X2
       have i₂ := eq105 (τ (τ (M.op X0 (M.op X0 (M.op X1 X0))))) X0 X1
       grind)
    | exact superpose eq105 eq316
    | (have j0 := eq316 (τ (τ (M.op X0 (M.op X0 (M.op X1 X0))))) X2
       grind)
    | exact resolve eq316 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq316
  have eq500 : ∀ X0 X1 X2 : G, (k X2 (σ (τ (τ (M.op X0 (M.op X0 (M.op X1 X0))))))) = (M.op X2 (σ (τ (τ (M.op X0 (M.op X0 (M.op X1 X0))))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq493 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq506 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 (M.op X0 (M.op X1 X0))))) = (M.op X2 (σ (M.op X0 (M.op X0 (M.op X1 X0))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq487 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq512 : ∀ X0 X1 X2 : G, (k X2 (τ (M.op X0 (M.op X0 (M.op X1 X0))))) = (M.op X2 (τ (M.op X0 (M.op X0 (M.op X1 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq500 X0 X1 X2
       have i₂ := eq11 (τ (M.op X0 (M.op X0 (M.op X1 X0))))
       grind)
    | exact superpose eq11 eq500
    | exact resolve eq500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq518 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X0 (M.op X1 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq506 X0 X1 X2
       have i₂ := eq71 X2 X0 X1
       grind)
    | exact superpose eq71 eq506
    | exact resolve eq506 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq506
  have eq523 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 (M.op X0 (M.op X1 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq512 X0 X1 X2
       have i₂ := eq72 X2 X0 X1
       grind)
    | exact superpose eq72 eq512
    | exact resolve eq512 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq512
  have eq1563 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1)))))))
       have i₂ := eq223 (σ X0) X1 X2
       grind)
    | exact superpose eq223 eq30
    | exact resolve eq30 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq1576 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1))))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1563 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1563
    | exact resolve eq1563 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563
  have eq2617 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1)))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (τ (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1))))))))
       have i₂ := eq1576 (σ X0) X1 X2
       grind)
    | exact superpose eq1576 eq30
    | exact resolve eq30 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576
  have eq2631 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1)))))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2617 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2617
    | exact resolve eq2617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2617
  have eq3525 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (τ (τ (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1)))))))))
       have i₂ := eq2631 (σ X0) X1 X2
       grind)
    | exact superpose eq2631 eq30
    | exact resolve eq30 eq2631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631
  have eq3541 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (τ (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1))))))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3525 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3525
    | exact resolve eq3525 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3525
  have eq3859 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (k (σ X1) X2) (σ (τ X0))) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (k X1 (τ X2))
       have i₂ := eq296 X1 X2 (τ X0)
       grind)
    | exact superpose eq296 eq17
    | (have j1 := eq296 X1 X2 (τ X0)
       grind)
    | exact resolve eq17 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq296
  have eq3884 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (k (σ X1) X2) (σ (τ X0))) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3859 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3859
    | (have j0 := eq3859 X0 X1 X2
       grind)
    | exact resolve eq3859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3859
  have eq3905 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (k (σ X1) X2) (σ (τ X0))) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3884 X0 X1 X2
       have i₂ := eq18 X2 X1
       grind)
    | exact superpose eq18 eq3884
    | (have j0 := eq3884 X0 X1 X2
       grind)
    | exact resolve eq3884 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3884
  have eq3921 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (k (σ X1) X2) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3905 X0 X1 X2
       have j1 := eq12 X0 (k (σ X1) X2)
       grind)
    | (have r₁ := eq3905 X0 X1 X2
       have r₂ := eq12 X0 (k (σ X1) X2)
       grind)
    | exact resolve eq3905 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3905
  have eq3937 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (M.op (k (σ X1) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3921 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3921
    | (have j0 := eq3921 X0 X1 X2
       grind)
    | exact resolve eq3921 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3921
  have eq4935 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1)))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (τ (τ (τ (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1))))))))))
       have i₂ := eq3541 (σ X0) X1 X2
       grind)
    | exact superpose eq3541 eq30
    | exact resolve eq30 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3541
  have eq4952 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (τ (τ (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op X2 X1)))))))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4935 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4935
    | exact resolve eq4935 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4935
  have eq12796 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3937 X0 X1 (τ (τ (τ (τ (τ (τ (τ (τ (M.op X1 (M.op X1 (M.op x X1)))))))))))
       have i₂ := eq4952 (σ X1) X1 x
       grind)
    | exact superpose eq4952 eq3937
    | exact resolve eq3937 eq4952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937 eq4952
  have eq12862 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12796 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12796
    | exact resolve eq12796 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12929 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12796 X1 (σ X0)
       grind)
    | exact superpose eq12796 eq15
    | (have j1 := eq12796 X1 (σ X0)
       grind)
    | exact resolve eq15 eq12796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12796
  have eq13039 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12862 (τ X1) X0
       grind)
    | exact superpose eq12862 eq18
    | (have j1 := eq12862 (τ X1) X0
       grind)
    | exact resolve eq18 eq12862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq12862
  have eq13698 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13039 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13039
    | exact resolve eq13039 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13039
  have eq13767 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13698 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq13698
    | (have j0 := eq13698 X0 X1
       grind)
    | exact resolve eq13698 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13698
  have eq14765 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12929 x y
       grind)
    | exact superpose eq12929 eq16
    | (have j1 := eq12929 x y
       grind)
    | exact resolve eq16 eq12929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12929
  have eq15076 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14765
       have i₂ := eq13767 y x
       grind)
    | exact superpose eq13767 eq14765
    | (have j1 := eq13767 (σ y) (σ x)
       grind)
    | (have r₁ := eq14765
       have r₂ := eq13767 y x
       grind)
    | exact resolve eq14765 eq13767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13767 eq14765
  have eq15079 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq15076
  have eq15082 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (M.op X0 (M.op x (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq15079
       grind)
    | exact superpose eq15079 eq9
    | exact resolve eq9 eq15079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15323 : ∀ X0 X1 : G, (M.op X1 (M.op x (M.op x x))) = X1 ∨ (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq15082 X1
       grind)
    | exact superpose eq15082 eq9
    | (have j1 := eq15082 X1
       grind)
    | exact resolve eq9 eq15082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15082
  have eq60088 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ x) (M.op (σ x) (σ x)))) = X2 ∨ (M.op X0 (M.op x (M.op x X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 X1 x x
       have i₂ := eq15323 X0 x
       grind)
    | exact superpose eq15323 eq19
    | (have j1 := eq15323 X2 X1
       grind)
    | exact resolve eq19 eq15323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq15323
  have eq70589 : ∀ X0 X1 X2 : G, (M.op X0 (τ (σ x))) = X0 ∨ (M.op X1 (M.op x (M.op x X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq523 (σ x) (σ x) X0
       have i₂ := eq60088 X1 X2 (σ x)
       grind)
    | exact superpose eq60088 eq523
    | (have j1 := eq60088 X1 X2 X2
       grind)
    | exact resolve eq523 eq60088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq60088
  have eq70956 : ∀ X0 X1 X2 : G, (M.op X0 x) = X0 ∨ (M.op X1 (M.op x (M.op x X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70589 X0 X1 X2
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq70589
    | (have j0 := eq70589 X0 X1 X2
       grind)
    | exact resolve eq70589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70589
  have eq71349 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op x (M.op x X0))) = X1 ∨ (M.op X2 (M.op x (M.op x X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 x X0
       have i₂ := eq70956 X0 X2 X3
       grind)
    | exact superpose eq70956 eq9
    | (have j1 := eq70956 X0 X1 X0
       grind)
    | exact resolve eq9 eq70956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70956
  have eq78773 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op x (M.op x X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq71349 X1 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71349
  have eq78774 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op x X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq78773 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78773
  have eq78979 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq78774 x x
       grind)
    | exact superpose eq78774 eq9
    | exact resolve eq9 eq78774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79011 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq518 x x X0
       have i₂ := eq78774 x x
       grind)
    | exact superpose eq78774 eq518
    | exact resolve eq518 eq78774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq78774
  have eq79606 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq15079
       have i₂ := eq78979 y
       grind)
    | exact superpose eq78979 eq15079
    | exact resolve eq15079 eq78979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15079
  have eq79608 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq79606
       have i₂ := eq79011 (σ y)
       grind)
    | exact superpose eq79011 eq79606
    | exact resolve eq79606 eq79011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79606
  have eq86004 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79608
       grind)
    | exact superpose eq79608 eq16
    | exact resolve eq16 eq79608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79608
  have eq86037 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86004
       have i₂ := eq78979 x
       grind)
    | exact superpose eq78979 eq86004
    | exact resolve eq86004 eq78979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86004
  have eq86039 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq86037
       have r₂ := eq79011 (σ x)
       grind)
    | exact resolve eq86037 eq79011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86037
  have eq86772 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86039
       grind)
    | exact superpose eq86039 eq16
    | exact resolve eq16 eq86039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86790 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq86039
       grind)
    | exact superpose eq86039 eq10
    | exact resolve eq10 eq86039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86039
  have eq86958 : x = y := by
    first
    | (have i₁ := eq86790
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq86790
    | exact resolve eq86790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86790
  have eq86959 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq86772
       have i₂ := eq79011 (σ x)
       grind)
    | exact superpose eq79011 eq86772
    | exact resolve eq86772 eq79011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79011 eq86772
  have eq86974 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq86959
       have i₂ := eq86958
       grind)
    | exact superpose eq86958 eq86959
    | exact resolve eq86959 eq86958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86958 eq86959
  have eq86989 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq86974
       have i₂ := eq78979 x
       grind)
    | exact superpose eq78979 eq86974
    | exact resolve eq86974 eq78979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78979 eq86974
  have eq86990 : False := by grind
  exact eq86990

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation443 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq96 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq333 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq96 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 (k (σ X1) (σ X0)) (M.op (σ X0) (σ X1))
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq355 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq333 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq356 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq355 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq362 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq356 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq356
    | (have j0 := eq356 X0 X1
       grind)
    | exact resolve eq356 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq363 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq362 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq745 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq363 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq363
    | exact resolve eq363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq363 x y
       grind)
    | exact superpose eq363 eq16
    | (have j1 := eq363 x y
       grind)
    | exact resolve eq16 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq781 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq745 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq745
    | (have j0 := eq745 X0 X1
       grind)
    | exact resolve eq745 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq745
  have eq876 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq781 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq781
    | exact resolve eq781 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq974 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq754
       have i₂ := eq876 x y
       grind)
    | exact superpose eq876 eq754
    | (have j1 := eq876 (σ x) (σ y)
       grind)
    | (have r₁ := eq754
       have r₂ := eq876 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq754
       have r₂ := eq876 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq754 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754 eq876
  have eq977 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq974
  have eq1024 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq977
       grind)
    | exact superpose eq977 eq10
    | exact resolve eq10 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1059 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1024
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1024
    | exact resolve eq1024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1060 : x = y := by grind
  clear eq1059
  have eq1062 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
  have eq1063 : False := by grind
  exact eq1063

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation443 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law443 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq2226 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2319 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2226 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2226
  have eq2320 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2319 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319
  have eq2740 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2320 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320
  have eq2743 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2740 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq2740 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq2740 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq2740 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq2740 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2740
  have eq2843 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq2743 X0 (τ X1)
       grind)
    | exact superpose eq2743 eq19
    | (have j1 := eq2743 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq2743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2846 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2743 (σ X0) (σ X1)
       grind)
    | exact superpose eq2743 eq15
    | (have j1 := eq2743 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq2743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2743
  have eq2938 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2843 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2843
    | exact resolve eq2843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2843
  have eq2990 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2938 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2938
    | (have j0 := eq2938 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq2938 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938
  have eq3284 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2846 x y
       grind)
    | exact superpose eq2846 eq16
    | (have j1 := eq2846 x y
       grind)
    | exact resolve eq16 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846
  have eq3337 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3284
       have i₂ := eq2990 y x
       grind)
    | exact superpose eq2990 eq3284
    | (have j1 := eq2990 (σ x) (σ y)
       grind)
    | (have r₁ := eq3284
       have r₂ := eq2990 y x
       grind)
    | (have r₁ := eq3284
       have r₂ := eq2990 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3284
       have r₂ := eq2990 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3284 eq2990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2990 eq3284
  have eq3338 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3337
  have eq3342 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3338
       grind)
    | exact superpose eq3338 eq10
    | exact resolve eq10 eq3338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq3386 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3342
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3342
    | exact resolve eq3342 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342
  have eq3387 : x = y := by grind
  clear eq3386
  have eq3389 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3387
       grind)
    | exact superpose eq3387 eq16
    | exact resolve eq16 eq3387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387
  have eq3390 : False := by grind
  exact eq3390

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_x_pyx_Equation443 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op X0 (M.op y (M.op y (M.op x y)))) = X0 := by
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
  have eq176 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 (k X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ y = (k y x) := by
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
  have eq936 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq957 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq936
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq936
    | exact resolve eq936 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq958 : (M.op x y) ≠ (k x x) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq935
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq935
    | exact resolve eq935 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq959 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq960 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1016 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq960
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq960
    | exact resolve eq960 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq1017 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq959
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq959
    | exact resolve eq959 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq1034 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1017
       grind)
    | exact superpose eq1017 eq39
    | exact resolve eq39 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1035 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1034
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1034
    | exact resolve eq1034 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1037 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq1035
    | exact resolve eq1035 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq1037 eq1016
    | exact resolve eq1016 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1047 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq1040
       have r₂ := eq27
       grind)
    | exact resolve eq1040 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1051 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq1047 eq957
    | (have r₁ := eq957
       have r₂ := eq1047
       grind)
    | exact resolve eq957 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957 eq1047
  have eq1056 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq1051
  have eq1057 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq1056
  have eq1062 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq1057 eq1037
    | exact resolve eq1037 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1066 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq1057 eq141
    | exact resolve eq141 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1057
  have eq1068 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1062
  have eq1071 : y = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq1066
    | exact resolve eq1066 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq1074 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1071
       have r₂ := eq958
       grind)
    | exact resolve eq1071 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958 eq1071
  have eq1080 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1074
       grind)
    | exact superpose eq1074 eq39
    | exact resolve eq39 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1083 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1080
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1080
    | exact resolve eq1080 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080
  have eq1089 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1083 eq1016
    | exact resolve eq1016 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016 eq1083
  have eq1093 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1089
  have eq1103 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1068
       grind)
    | exact superpose eq1068 eq39
    | exact resolve eq39 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1107 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1103
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1103
    | exact resolve eq1103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1109 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq1107
    | exact resolve eq1107 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1093 eq1109
    | exact resolve eq1109 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093 eq1109
  have eq1145 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1137
  have eq1149 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1145
       have r₂ := eq27
       grind)
    | exact resolve eq1145 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq1152 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1149 eq176
    | exact resolve eq176 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1154 : ∀ X0 : G, (M.op X0 (M.op (σ y) (k (σ y) (σ y)))) = X0 ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1152 X0
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq1152
    | exact resolve eq1152 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1315 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f1315_16 : ∀ X0 : G, (M.op X0 (M.op (σ y) (k (σ y) (σ y)))) = X0 ∨ y = x ∨ (σ y) = (σ x) ∨ (σ y) = (σ (M.op x y)) := by
      intro X0
      grind
    have f1315_21 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
      intro X0 X1
      grind
    have f1315_24 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
      intro X0 X1 X2
      grind
    have f1315_25 : X0 ≠ (M.op X0 (σ y)) := by grind
    have f1315_26 : y ≠ x := by grind
    have f1315_27 : (σ y) ≠ (σ x) := by grind
    have f1315_28 : (σ y) ≠ (σ (M.op x y)) := by grind
    have f1315_30 : ∀ X0 : G, (M.op X0 (M.op (σ y) (k (σ y) (σ y)))) = X0 ∨ (σ y) = (σ x) ∨ (σ y) = (σ (M.op x y)) := by
      intro X0
      first
      | (have j0 := f1315_16 X0
         grind)
      | (have r₁ := f1315_16 X0
         have r₂ := f1315_26
         grind)
      | exact resolve f1315_16 f1315_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1315_32 : ∀ X0 : G, (M.op X0 (M.op (σ y) (k (σ y) (σ y)))) = X0 ∨ (σ y) = (σ (M.op x y)) := by
      intro X0
      first
      | (have j0 := f1315_30 X0
         grind)
      | (have r₁ := f1315_30 X0
         have r₂ := f1315_27
         grind)
      | exact resolve f1315_30 f1315_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1315_33 : ∀ X0 : G, (M.op X0 (M.op (σ y) (k (σ y) (σ y)))) = X0 := by
      intro X0
      first
      | (have j0 := f1315_32 X0
         grind)
      | (have r₁ := f1315_32 X0
         have r₂ := f1315_28
         grind)
      | exact resolve f1315_32 f1315_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1315_34 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
      intro X0
      grind
    have f1315_51 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
      intro X0
      first
      | (have i₁ := f1315_24 X0 (σ y) (σ y)
         have i₂ := f1315_34 (σ y)
         grind)
      | exact superpose f1315_34 f1315_24
      | exact resolve f1315_24 f1315_34
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1315_59 : X0 ≠ X0 := by
      first
      | (have i₁ := f1315_25
         have i₂ := f1315_51 X0
         grind)
      | exact superpose f1315_51 f1315_25
      | (have r₁ := f1315_25
         have r₂ := f1315_51 X0
         grind)
      | exact resolve f1315_25 f1315_51
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1315_60 : False := by grind
    exact f1315_60
  clear eq1154
  have eq1336 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1315 eq26
    | (have j1 := eq1315 (σ x)
       grind)
    | exact resolve eq26 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1347 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1336 eq1149
    | exact resolve eq1149 eq1336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149 eq1336
  have eq1352 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1347
  have eq1358 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1352 eq31
    | exact resolve eq31 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq1395 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq1358
    | exact resolve eq1358 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1358
  have eq1396 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1395
  have eq1462 : (M.op x y) = (τ (σ y)) ∨ x = y := by
    first
    | exact superpose eq1396 eq28
    | exact resolve eq28 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1396
  have eq1492 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1462
    | exact resolve eq1462 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1462
  have eq1495 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq1492
       grind)
    | exact superpose eq1492 eq18
    | exact resolve eq18 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1499 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq1492
       grind)
    | exact superpose eq1492 eq175
    | exact resolve eq175 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1503 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq1492
  have eq1507 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (k (M.op x y) (M.op x y)))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1499 X0
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq1499
    | exact resolve eq1499 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1817 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = y := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f1817_14 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (k (M.op x y) (M.op x y)))) = X0 ∨ x = y := by
      intro X0
      grind
    have f1817_19 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
      intro X0 X1
      grind
    have f1817_22 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
      intro X0 X1 X2
      grind
    have f1817_23 : X0 ≠ (M.op X0 (M.op x y)) := by grind
    have f1817_24 : x ≠ y := by grind
    have f1817_26 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (k (M.op x y) (M.op x y)))) = X0 := by
      intro X0
      first
      | (have j0 := f1817_14 X0
         grind)
      | (have r₁ := f1817_14 X0
         have r₂ := f1817_24
         grind)
      | exact resolve f1817_14 f1817_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1817_28 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) = X0 := by
      intro X0
      grind
    have f1817_59 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 := by
      intro X0
      first
      | (have i₁ := f1817_22 X0 (M.op x y) (M.op x y)
         have i₂ := f1817_28 (M.op x y)
         grind)
      | exact superpose f1817_28 f1817_22
      | exact resolve f1817_22 f1817_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1817_70 : X0 ≠ X0 := by
      first
      | (have i₁ := f1817_23
         have i₂ := f1817_59 X0
         grind)
      | exact superpose f1817_59 f1817_23
      | (have r₁ := f1817_23
         have r₂ := f1817_59 X0
         grind)
      | exact resolve f1817_23 f1817_59
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1817_71 : False := by grind
    exact f1817_71
  clear eq181 eq1507
  have eq1841 : x = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1817 eq1495
    | exact resolve eq1495 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495 eq1817
  have eq1848 : x = (M.op x y) ∨ x = y := by grind
  clear eq1841
  have eq1852 : x = y := by
    first
    | (have r₁ := eq1848
       have r₂ := eq1503
       grind)
    | exact resolve eq1848 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503 eq1848
  have eq1860 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1852
       grind)
    | exact superpose eq1852 eq18
    | exact resolve eq18 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1861 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1852
       grind)
    | exact superpose eq1852 eq24
    | exact resolve eq24 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1852
  have eq1868 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1861
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1861
    | exact resolve eq1861 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861
  have eq1869 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1860
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1860
    | exact resolve eq1860 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1860
  have eq1870 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1868 eq26
    | exact resolve eq26 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1868
  have eq1909 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1870
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1870
    | exact resolve eq1870 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq1870
  have eq1915 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1869
       grind)
    | exact superpose eq1869 eq39
    | exact resolve eq39 eq1869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1869
  have eq1919 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1915
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1915
    | exact resolve eq1915 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1915
  have eq1921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1909 eq1919
    | exact resolve eq1919 eq1909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909 eq1919
  have eq1923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1921
    | exact resolve eq1921 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1921
  have eq1925 : False := by grind
  exact eq1925

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_pyx_pxy_Equation443 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law443 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq101 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (σ X0)) (M.op (σ (σ X0)) (σ (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq101
    | exact resolve eq101 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) (M.op (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq102 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) X1
       have i₂ := eq101 X0 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))
       grind)
    | exact superpose eq101 eq102
    | exact resolve eq102 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))) (M.op (τ (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))) (τ (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq102 (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))) X1
       have i₂ := eq102 X0 (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))
       grind)
    | exact superpose eq102 eq102
    | exact resolve eq102 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))) (τ (M.op (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))) (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq173 X0 X1
       have i₂ := eq63 (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))
       grind)
    | exact superpose eq63 eq173
    | exact resolve eq173 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq187 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) (τ (M.op (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq172 X0 X1
       have i₂ := eq63 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))
       grind)
    | exact superpose eq63 eq172
    | exact resolve eq172 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq194 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))) (τ (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 X1
       have i₂ := eq102 X0 (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))
       grind)
    | exact superpose eq102 eq186
    | exact resolve eq186 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq195 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 X1
       have i₂ := eq101 X0 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))
       grind)
    | exact superpose eq101 eq187
    | exact resolve eq187 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq202 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))) (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 X1
       have i₂ := eq63 (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))
       grind)
    | exact superpose eq63 eq194
    | exact resolve eq194 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq203 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq63 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))
       grind)
    | exact superpose eq63 eq195
    | exact resolve eq195 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq208 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0 X1
       have i₂ := eq102 X0 (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))
       grind)
    | exact superpose eq102 eq202
    | exact resolve eq202 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq202
  have eq209 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 X1
       have i₂ := eq101 X0 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))
       grind)
    | exact superpose eq101 eq203
    | exact resolve eq203 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq203
  have eq382 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq3120 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq108 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq108
    | exact resolve eq108 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq6580 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq382 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq382
    | (have j0 := eq382 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq382 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq33931 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (τ (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0))))))) (M.op (τ (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0))))))) (τ (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq208 (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0)))))) X1
       have i₂ := eq3120 X0 (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0))))))
       grind)
    | exact superpose eq3120 eq208
    | exact resolve eq208 eq3120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq34030 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (τ (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0))))))) (τ (M.op (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0)))))) (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33931 X0 X1
       have i₂ := eq63 (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0))))))
       grind)
    | exact superpose eq63 eq33931
    | exact resolve eq33931 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33931
  have eq34141 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (τ (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0))))))) (τ (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0)))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34030 X0 X1
       have i₂ := eq3120 X0 (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0))))))
       grind)
    | exact superpose eq3120 eq34030
    | exact resolve eq34030 eq3120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34030
  have eq34248 : ∀ X0 X1 : G, (M.op X1 (τ (τ (M.op (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0)))))) (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0)))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34141 X0 X1
       have i₂ := eq63 (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0))))))
       grind)
    | exact superpose eq63 eq34141
    | exact resolve eq34141 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq34141
  have eq34353 : ∀ X0 X1 : G, (M.op X1 (τ (τ (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34248 X0 X1
       have i₂ := eq3120 X0 (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ X0))) (σ (σ (σ (M.op X0 X0))))))
       grind)
    | exact superpose eq3120 eq34248
    | exact resolve eq34248 eq3120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120 eq34248
  have eq47300 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq6580 x y
       grind)
    | exact superpose eq6580 eq16
    | (have j1 := eq6580 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq6580 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq6580 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq6580 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq6580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6580
  have eq47401 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq47300
  have eq61377 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq47401
       grind)
    | exact superpose eq47401 eq9
    | exact resolve eq9 eq47401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61378 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq47401
       grind)
    | exact superpose eq47401 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq47401
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq47401
       grind)
    | exact resolve eq13 eq47401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61417 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq61378
  have eq61418 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq61417
  have eq61465 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq61418
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq61418
    | exact resolve eq61418 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61418
  have eq61466 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ (M.op x x)))) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq61377 X0
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq61377
    | exact resolve eq61377 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61377
  have eq61487 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq14 eq61465
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq61465 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61465
  have eq61494 : (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq61487
       grind)
    | exact superpose eq61487 eq10
    | exact resolve eq10 eq61487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61487
  have eq61660 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq61494
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq61494
    | exact resolve eq61494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61494
  have eq61661 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq61660
       grind)
    | exact superpose eq61660 eq9
    | exact resolve eq9 eq61660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61660
  have eq140307 : ∀ X0 : G, x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq61661 x
       grind)
    | exact superpose eq61661 eq9
    | exact resolve eq9 eq61661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61661
  have eq140818 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op y x))) = X0 ∨ (σ x) = (σ y) ∨ (M.op X1 x) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq140307 X1
       grind)
    | exact superpose eq140307 eq9
    | (have j1 := eq140307 X1
       grind)
    | exact resolve eq9 eq140307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140307
  have eq303553 : ∀ X0 : G, (M.op X0 (τ (σ x))) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq209 x X0
       have i₂ := eq61466 (σ x)
       grind)
    | exact superpose eq61466 eq209
    | exact resolve eq209 eq61466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq61466
  have eq303606 : ∀ X0 : G, x = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq303553 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq303553
    | exact resolve eq303553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303553
  have eq304081 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = X0 ∨ (σ x) = (σ y) ∨ (M.op X1 x) = X1 ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq303606 eq140818
    | (have j0 := eq140818 X0 X1
       have j1 := eq303606 X1
       grind)
    | exact resolve eq140818 eq303606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140818
  have eq304152 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (M.op X0 x) = X0 ∨ (M.op X1 x) = X1 ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq303606 eq304081
    | (have j0 := eq304081 X0 X0
       have j1 := eq303606 X0
       grind)
    | exact resolve eq304081 eq303606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303606 eq304081
  have eq304162 : ∀ X0 X1 : G, y = (τ (σ x)) ∨ (M.op X0 x) = X0 ∨ (M.op X1 x) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq10 y
       have i₂ := eq304152 X0 X1
       grind)
    | exact superpose eq304152 eq10
    | (have j1 := eq304152 X0 X0
       grind)
    | exact resolve eq10 eq304152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304152
  have eq304399 : ∀ X0 X1 : G, x = y ∨ (M.op X0 x) = X0 ∨ (M.op X1 x) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq304162 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq304162
    | (have j0 := eq304162 X0 X0
       grind)
    | exact resolve eq304162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304162
  have eq304400 : ∀ X0 X1 : G, (M.op X1 x) = X1 ∨ (M.op X0 x) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq304399 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304399
  have eq304614 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 x) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq304400 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304400
  have eq304615 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq304614 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304614
  have eq305431 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq304615 eq47401
    | exact resolve eq47401 eq304615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47401
  have eq305532 : ∀ X0 : G, (M.op X0 (τ (τ (M.op (σ (σ (σ x))) (M.op (σ (σ (σ x))) (σ (σ (σ x)))))))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq34353 x X0
       have i₂ := eq304615 x
       grind)
    | exact superpose eq304615 eq34353
    | exact resolve eq34353 eq304615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34353
  have eq305646 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq305431
  have eq305686 : ∀ X0 : G, (M.op X0 (τ (τ (M.op (σ (σ (σ x))) (σ (M.op (σ (σ x)) (σ (σ x)))))))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq305532 X0
       have i₂ := eq22 (σ (σ x))
       grind)
    | exact superpose eq22 eq305532
    | exact resolve eq305532 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305532
  have eq305798 : ∀ X0 : G, (M.op X0 (τ (τ (M.op (σ (σ (σ x))) (σ (σ (M.op (σ x) (σ x)))))))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq305686 X0
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq305686
    | exact resolve eq305686 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305686
  have eq305904 : ∀ X0 : G, (M.op X0 (τ (τ (M.op (σ (σ (σ x))) (σ (σ (σ (M.op x x)))))))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq305798 X0
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq305798
    | exact resolve eq305798 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305798
  have eq306010 : ∀ X0 : G, (M.op X0 (τ (τ (M.op (σ (σ (σ x))) (σ (σ (σ x))))))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq304615 eq305904
    | exact resolve eq305904 eq304615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305904
  have eq306115 : ∀ X0 : G, (M.op X0 (τ (τ (σ (M.op (σ (σ x)) (σ (σ x))))))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq306010 X0
       have i₂ := eq22 (σ (σ x))
       grind)
    | exact superpose eq22 eq306010
    | exact resolve eq306010 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306010
  have eq306186 : ∀ X0 : G, (M.op X0 (τ (M.op (σ (σ x)) (σ (σ x))))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq306115 X0
       have i₂ := eq10 (M.op (σ (σ x)) (σ (σ x)))
       grind)
    | exact superpose eq10 eq306115
    | exact resolve eq306115 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306115
  have eq306232 : ∀ X0 : G, (M.op X0 (τ (σ (M.op (σ x) (σ x))))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq306186 X0
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq306186
    | exact resolve eq306186 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306186
  have eq306260 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq306232 X0
       have i₂ := eq10 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq10 eq306232
    | exact resolve eq306232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306232
  have eq306285 : ∀ X0 : G, (M.op X0 (σ (M.op x x))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq306260 X0
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq306260
    | exact resolve eq306260 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306260
  have eq306293 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq304615 eq306285
    | exact resolve eq306285 eq304615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304615 eq306285
  have eq306695 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq306293 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306293
  have eq307649 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq305646
       have i₂ := eq306695 (σ y)
       grind)
    | exact superpose eq306695 eq305646
    | exact resolve eq305646 eq306695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305646 eq306695
  have eq307667 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq307649
  have eq308549 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq307667
       grind)
    | exact superpose eq307667 eq10
    | exact resolve eq10 eq307667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307667
  have eq308795 : x = y ∨ x = y := by
    first
    | (have i₁ := eq308549
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq308549
    | exact resolve eq308549 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308549
  have eq308796 : x = y := by grind
  clear eq308795
  have eq308826 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq308796
       grind)
    | exact superpose eq308796 eq16
    | exact resolve eq16 eq308796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308796
  have eq308827 : False := by grind
  exact eq308827

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq177 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq38 (M.op sF0 sF0)
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq38
    | exact resolve eq38 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq181 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq180
    | exact resolve eq180 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq209 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq175
  have eq220 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq209
    | exact resolve eq209 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq690 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4 X5
       have i₂ := eq16 X2 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X2 X3 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq694 x x X2 X3 X5
       have i₂ := eq696 x x
       grind)
    | exact superpose eq696 eq694
    | exact resolve eq694 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq703 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq700 x x X5
       have i₂ := eq696 x x
       grind)
    | exact superpose eq696 eq700
    | exact resolve eq700 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq704 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq695 X0 (M.op X0 x)
       have i₂ := eq695 X0 x
       grind)
    | exact superpose eq695 eq695
    | exact resolve eq695 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq695 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq695
    | (have j0 := eq695 x y
       grind)
    | exact resolve eq695 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : (M.op (M.op x y) y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq695
    | (have j0 := eq695 (σ x) (σ y)
       grind)
    | exact resolve eq695 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq695 x x
       grind)
    | exact superpose eq695 eq16
    | exact resolve eq16 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq695 x x
       have i₂ := eq696 x x
       grind)
    | exact superpose eq696 eq695
    | exact resolve eq695 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq696
  have eq765 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq735 eq703
    | exact resolve eq703 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq858 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ X0 ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq703 eq13
    | (have j0 := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq703 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq13 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq863 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq703 eq28
    | (have j0 := eq28 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq28 x (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq703 x
       grind)
    | exact resolve eq28 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq703
  have eq866 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq863 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq868 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq735 eq866
    | exact resolve eq866 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq870 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq735 eq858
    | (have j0 := eq858 X0
       grind)
    | (have r₁ := eq858 (M.op (M.op x y) y)
       have r₂ := eq735
       grind)
    | exact resolve eq858 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq874 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op x y) y) ≠ X0 := by
    intro X0
    first
    | exact superpose eq735 eq870
    | (have j0 := eq870 X0
       grind)
    | (have r₁ := eq870 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq735
       grind)
    | exact resolve eq870 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq998 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op x y) y) = X0 ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq704 eq11
    | (have j0 := eq11 (M.op (M.op x y) y) X0
       grind)
    | exact resolve eq11 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1008 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq998 X0
       have j1 := eq874 X0
       grind)
    | (have r₁ := eq998 X0
       have r₂ := eq874 (k (M.op (M.op x y) y) X0)
       grind)
    | (have r₁ := eq998 X0
       have r₂ := eq874 X0
       grind)
    | (have r₁ := eq998 (M.op (M.op x y) y)
       have r₂ := eq874 (M.op (M.op x y) y)
       grind)
    | exact resolve eq998 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq998
  have eq1010 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq1008 X0
       have j1 := eq13 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq1008 x
       have r₂ := eq13 (M.op (M.op x y) y) x
       grind)
    | (have r₁ := eq1008 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))
       grind)
    | exact resolve eq1008 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1130 : (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) (σ x)) := by
    first
    | exact superpose eq1010 eq40
    | exact resolve eq40 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1132 : (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1010 eq42
    | exact resolve eq42 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq1010
  have eq3317 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq765
       grind)
    | exact superpose eq765 eq40
    | exact resolve eq40 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq3319 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3317
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3317
    | exact resolve eq3317 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317
  have eq3321 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq3319
    | exact resolve eq3319 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3319
  have eq3330 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3321 eq767
    | exact resolve eq767 eq3321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3338 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq3330
       have r₂ := eq27
       grind)
    | exact resolve eq3330 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3330
  have eq3343 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3338 eq220
    | exact resolve eq220 eq3338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq3338
  have eq3379 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq3343
    | exact resolve eq3343 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3343
  have eq3390 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq3379
       have r₂ := eq176
       grind)
    | exact resolve eq3379 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq3379
  have eq3394 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq3390
       have r₂ := eq13 y x
       grind)
    | exact resolve eq3390 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3390
  have eq3398 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq3394
       grind)
    | exact superpose eq3394 eq40
    | exact resolve eq40 eq3394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3394
  have eq3399 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3398
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3398
    | exact resolve eq3398 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3398
  have eq3401 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq3399
       have r₂ := eq177
       grind)
    | exact resolve eq3399 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq3399
  have eq3405 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3401 eq3321
    | exact resolve eq3321 eq3401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321
  have eq3406 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3401 eq767
    | exact resolve eq767 eq3401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq3401
  have eq3544 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq3405
       grind)
    | exact superpose eq3405 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq3405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3557 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq710 y y
       have i₂ := eq3405
       grind)
    | exact superpose eq3405 eq710
    | exact resolve eq710 eq3405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3405
  have eq3561 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3544
  have eq3565 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3557
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3557
    | exact resolve eq3557 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3557
  have eq3607 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3406 eq710
    | exact resolve eq710 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406
  have eq3615 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3607
    | exact resolve eq3607 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3607
  have eq3701 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq3565 eq868
    | exact resolve eq868 eq3565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq3723 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3565 eq1132
    | exact resolve eq1132 eq3565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq3787 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq3723
    | exact resolve eq3723 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3723
  have eq3981 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3615 eq3565
    | exact resolve eq3565 eq3615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3615
  have eq4598 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3787 eq794
    | (have j0 := eq794 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq794 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq3787
       grind)
    | exact resolve eq794 eq3787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3787
  have eq4599 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4598
  have eq4600 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4599
  have eq5519 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4600 eq710
    | exact resolve eq710 eq4600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5527 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3565 eq5519
    | exact resolve eq5519 eq3565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5519
  have eq5617 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5527 eq4600
    | exact resolve eq4600 eq5527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4600 eq5527
  have eq5641 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq5617
  have eq5674 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq5641 eq29
    | exact resolve eq29 eq5641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5701 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq5641
  have eq5718 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq5674
    | exact resolve eq5674 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5674
  have eq11744 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3981 eq708
    | exact resolve eq708 eq3981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708 eq3981
  have eq11762 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11744
    | exact resolve eq11744 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11744
  have eq11765 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3565 eq11762
    | exact resolve eq11762 eq3565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11762
  have eq11766 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq11765
  have eq12047 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11766 eq735
    | exact resolve eq735 eq11766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq11766
  have eq12057 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12047
    | exact resolve eq12047 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12047
  have eq12065 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3565 eq12057
    | exact resolve eq12057 eq3565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3565 eq12057
  have eq12066 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq12065
  have eq12073 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12066 eq29
    | exact resolve eq29 eq12066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12066
  have eq12155 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq12073
    | exact resolve eq12073 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq12073
  have eq12167 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12155 eq27
    | exact resolve eq27 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12155
  have eq12236 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12167
       have r₂ := eq5718
       grind)
    | exact resolve eq12167 eq5718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5718 eq12167
  have eq12241 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12236
       grind)
    | exact superpose eq12236 eq18
    | exact resolve eq18 eq12236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12316 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3561
       have i₂ := eq12236
       grind)
    | exact superpose eq12236 eq3561
    | exact resolve eq3561 eq12236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3561
  have eq12331 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12316
  have eq12336 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3701 eq12331
    | exact resolve eq12331 eq3701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3701 eq12331
  have eq12337 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq12336
  have eq12348 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq707 eq12241
    | exact resolve eq12241 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq12241
  have eq12352 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12236 eq12348
    | exact resolve eq12348 eq12236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12348
  have eq12441 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12352 eq181
    | exact resolve eq181 eq12352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq12491 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq12441
    | exact resolve eq12441 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12441
  have eq12499 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12337 eq12491
    | exact resolve eq12491 eq12337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12337 eq12491
  have eq12532 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12499 eq794
    | (have j0 := eq794 (σ y) (σ y)
       grind)
    | (have r₁ := eq794 (σ y) (σ y)
       have r₂ := eq12499
       grind)
    | exact resolve eq794 eq12499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12499
  have eq12533 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12532
  have eq12534 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12533
  have eq12562 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq12534 eq690
    | exact resolve eq690 eq12534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12574 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12534 eq710
    | exact resolve eq710 eq12534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12598 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12236 eq12574
    | exact resolve eq12574 eq12236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12574
  have eq12610 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X2
    first
    | (have i₁ := eq12562 x x X2
       have i₂ := eq710 x x
       grind)
    | (have i₁ := eq12562 x y X2
       have i₂ := eq710 X2 x
       grind)
    | exact superpose eq710 eq12562
    | (have j0 := eq12562 x y X2
       grind)
    | exact resolve eq12562 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12562
  have eq12619 : (M.op x y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12352 eq12598
    | exact resolve eq12598 eq12352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12598
  have eq12628 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq12236 eq12610
    | exact resolve eq12610 eq12236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12610
  have eq12645 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq12352 eq12628
    | exact resolve eq12628 eq12352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12628
  have eq12651 : ∀ X2 : G, (M.op x y) = (M.op X2 (σ y)) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq12534 eq12645
    | exact resolve eq12645 eq12534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12645
  have eq12666 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12619 eq12534
    | exact resolve eq12534 eq12619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12534
  have eq12672 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq12619 eq690
    | exact resolve eq690 eq12619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq12619
  have eq12701 : (M.op x y) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq12666
  have eq12722 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    intro X2
    first
    | (have i₁ := eq12672 x x X2
       have i₂ := eq710 x x
       grind)
    | (have i₁ := eq12672 x y X2
       have i₂ := eq710 X2 x
       grind)
    | exact superpose eq710 eq12672
    | (have j0 := eq12672 x y X2
       grind)
    | exact resolve eq12672 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq12672
  have eq12743 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq12236 eq12722
    | exact resolve eq12722 eq12236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12236 eq12722
  have eq12753 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq12352 eq12743
    | exact resolve eq12743 eq12352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12352 eq12743
  have eq12759 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq12651 eq12753
    | exact resolve eq12753 eq12651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12651 eq12753
  have eq12763 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12701 eq26
    | exact resolve eq26 eq12701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12810 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12701 eq5701
    | (have r₁ := eq5701
       have r₂ := eq12701
       grind)
    | exact resolve eq5701 eq12701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5701 eq12701
  have eq12828 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq12810
  have eq12829 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq12828
  have eq12869 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12759 eq12763
    | exact resolve eq12763 eq12759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12759 eq12763
  have eq13021 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12869 eq27
    | exact resolve eq27 eq12869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12869
  have eq13077 : x = (M.op x y) := by
    first
    | (have r₁ := eq13021
       have r₂ := eq12829
       grind)
    | exact resolve eq13021 eq12829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12829 eq13021
  have eq13084 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq13077
       grind)
    | exact superpose eq13077 eq18
    | exact resolve eq18 eq13077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq13085 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq13077
       grind)
    | exact superpose eq13077 eq22
    | exact resolve eq22 eq13077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq13077
  have eq13106 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13085 eq20
    | exact resolve eq20 eq13085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13085
  have eq13260 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq13084 eq704
    | exact resolve eq704 eq13084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq13269 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq13084 eq850
    | exact resolve eq850 eq13084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq13290 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq13084 eq1130
    | exact resolve eq1130 eq13084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq13084
  have eq13368 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq13290
    | exact resolve eq13290 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq13290
  have eq13395 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq13106 eq13368
    | exact resolve eq13368 eq13106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13368
  have eq13467 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq13260 eq16
    | exact resolve eq16 eq13260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13260
  have eq13884 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13395 eq794
    | (have j0 := eq794 (σ x) (σ x)
       grind)
    | (have r₁ := eq794 (σ x) (σ x)
       have r₂ := eq13395
       grind)
    | exact resolve eq794 eq13395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq13395
  have eq13885 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq13884
  have eq13886 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq13885
  have eq14329 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq13886 eq697
    | exact resolve eq697 eq13886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq14357 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq13886 eq14329
    | exact resolve eq14329 eq13886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13886 eq14329
  have eq14370 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq14357 x x
       have i₂ := eq13467 x x
       grind)
    | exact superpose eq13467 eq14357
    | exact resolve eq14357 eq13467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13467 eq14357
  have eq14393 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq14370 eq26
    | exact resolve eq26 eq14370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq14460 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13269 eq14393
    | exact resolve eq14393 eq13269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13269 eq14393
  have eq14496 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq14460 eq27
    | exact resolve eq27 eq14460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14460
  have eq14550 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq13106 eq14496
    | exact resolve eq14496 eq13106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13106 eq14496
  have eq14553 : False := by grind
  exact eq14553
