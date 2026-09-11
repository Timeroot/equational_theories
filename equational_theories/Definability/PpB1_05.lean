import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pyy_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq23 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq15
    | exact resolve eq15 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq48
    | exact resolve eq48 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq53
    | exact resolve eq53 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq53
  have eq62 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq86 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq209 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq62 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq62 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq62 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq62 X0 X1
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ X0) (σ X1)) (M.op X2 (M.op X2 (σ X1)))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq62 X1 X0
       grind)
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq9
    | (have j1 := eq62 X1 X0
       grind)
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq231 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq209 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq232 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq231 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq236 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq232 X0 X1
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq232
    | (have j0 := eq232 X0 X1
       grind)
    | exact resolve eq232 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq232
  have eq245 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq236 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq236
    | (have j0 := eq236 X0 X1
       grind)
    | exact resolve eq236 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq724 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq86 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq86 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq86 eq9
    | exact resolve eq9 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1058 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq724 X0 x X1
       grind)
    | exact superpose eq724 eq9
    | exact resolve eq9 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq2499 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq245 (τ X0) (τ X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq245
    | (have j0 := eq245 (τ X1) (τ X0)
       grind)
    | exact resolve eq245 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq245
  have eq2672 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2499 X0 X1
       have i₂ := eq58 X1
       grind)
    | exact superpose eq58 eq2499
    | (have j0 := eq2499 X0 X1
       grind)
    | exact resolve eq2499 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq2499
  have eq2698 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2672 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2672
    | (have j0 := eq2672 X0 X1
       grind)
    | exact resolve eq2672 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2672
  have eq2716 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2698 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2698
    | (have j0 := eq2698 X0 X1
       grind)
    | exact resolve eq2698 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2698
  have eq2728 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2716 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2716
    | (have j0 := eq2716 X0 X1
       grind)
    | exact resolve eq2716 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716
  have eq2736 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2728 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2728
    | (have j0 := eq2728 X0 X1
       grind)
    | exact resolve eq2728 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2728
  have eq2739 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2736 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2736
    | (have j0 := eq2736 X0 X1
       grind)
    | exact resolve eq2736 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2736
  have eq2741 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2739 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2739
    | (have j0 := eq2739 X0 X1
       grind)
    | exact resolve eq2739 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2739
  have eq2742 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2741 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq2741 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2741 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2741
  have eq2874 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2742 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3060 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) ≠ (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq226 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq226
    | exact resolve eq226 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq3077 : ∀ X0 X1 : G, (k (σ X1) X0) ≠ (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3060 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3060
    | (have j0 := eq3060 X0 X1
       grind)
    | exact resolve eq3060 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3060
  have eq3081 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) ≠ (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3077 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3077
    | (have j0 := eq3077 X0 X1
       grind)
    | exact resolve eq3077 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3077
  have eq3085 : ∀ X0 X1 : G, (k (σ X1) X0) ≠ (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3081 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq3081 (σ X1) X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq3081 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq3081 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3081
  have eq4322 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X1) X0) (M.op X2 (M.op X2 X0))) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq216
    | exact resolve eq216 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq4432 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op (M.op (σ X1) X0) (M.op X2 (M.op X2 X0))) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4322 X0 X1 X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq4322
    | (have j0 := eq4322 X0 X1 X2
       grind)
    | exact resolve eq4322 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4322
  have eq4441 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X1) X0) (M.op X2 (M.op X2 X0))) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4432 X0 X1 X2
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq4432 X1 X1 X2
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq4432 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4432
  have eq35423 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3085 X1 X1
       have i₂ := eq2742 (σ X1) X1
       grind)
    | exact superpose eq2742 eq3085
    | (have j0 := eq3085 X0 X1
       have j1 := eq2742 (σ X1) X0
       grind)
    | (have r₁ := eq3085 (σ X1) X1
       have r₂ := eq2742 (σ X1) (σ X1)
       grind)
    | exact resolve eq3085 eq2742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2742 eq3085
  have eq35427 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35423 X0 X1
       have j1 := eq2874 (σ X1) X0
       grind)
    | (have r₁ := eq35423 (σ X1) X1
       have r₂ := eq2874 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq35423 X1 X1
       have r₂ := eq2874 (σ X1) X1
       grind)
    | exact resolve eq35423 eq2874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874 eq35423
  have eq54220 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1058 X0 (σ X1) (M.op x (M.op x X0))
       have i₂ := eq4441 X0 X1 x
       grind)
    | exact superpose eq4441 eq1058
    | (have j1 := eq4441 X0 X1 x
       grind)
    | exact resolve eq1058 eq4441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058 eq4441
  have eq54538 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq54220 X0 X1
       have j1 := eq35427 X0 X1
       grind)
    | (have r₁ := eq54220 X0 X1
       have r₂ := eq35427 X0 X1
       grind)
    | (have r₁ := eq54220 (σ X1) X1
       have r₂ := eq35427 (σ X1) X1
       grind)
    | exact resolve eq54220 eq35427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35427 eq54220
  have eq54640 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54538 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54538
    | exact resolve eq54538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54675 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq54538 (σ X0) X1
       grind)
    | exact superpose eq54538 eq15
    | exact resolve eq15 eq54538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54538
  have eq55990 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54675 x y
       grind)
    | exact superpose eq54675 eq16
    | exact resolve eq16 eq54675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54675
  have eq56460 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq55990
       have i₂ := eq54640 y x
       grind)
    | exact superpose eq54640 eq55990
    | exact resolve eq55990 eq54640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54640 eq55990
  have eq56461 : False := by grind
  exact eq56461

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
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
  have eq77 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq94 y x
       grind)
    | exact superpose eq94 eq73
    | (have j1 := eq94 y x
       grind)
    | exact resolve eq73 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120 eq94
    | (have j0 := eq94 (σ y) (σ x)
       grind)
    | exact resolve eq94 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq27
    | exact resolve eq27 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37
  have eq591 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq77
    | (have r₁ := eq77
       have r₂ := eq129
       grind)
    | exact resolve eq77 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq129
  have eq592 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq591
  have eq1233 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq592 eq120
    | exact resolve eq120 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq1237 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1233
  have eq1242 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1237
       have r₂ := eq131
       grind)
    | exact resolve eq1237 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq1237
  have eq1257 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1242 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1242
       grind)
    | exact resolve eq13 eq1242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1264 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1257 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1453 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1264 eq120
    | exact resolve eq120 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq1264
  have eq1456 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1453
  have eq1461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1456
    | exact resolve eq1456 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456
  have eq1463 : y = (M.op x y) := by
    first
    | (have r₁ := eq1461
       have r₂ := eq27
       grind)
    | exact resolve eq1461 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461
  have eq1466 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1463 eq20
    | exact resolve eq20 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1471 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq1463 eq76
    | (have r₁ := eq76
       have r₂ := eq1463
       grind)
    | exact resolve eq76 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1475 : y = (k y x) ∨ x = (M.op x x) := by grind
  clear eq1471
  have eq1482 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1466
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1466
    | exact resolve eq1466 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq1484 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1482 eq26
    | exact resolve eq26 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1797 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1475
       grind)
    | exact superpose eq1475 eq73
    | exact resolve eq73 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1475
  have eq1804 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1482 eq1797
    | exact resolve eq1797 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797
  have eq1806 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1804
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1804
    | exact resolve eq1804 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1804
  have eq1807 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1482 eq1806
    | exact resolve eq1806 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482 eq1806
  have eq1813 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1807 eq94
    | (have j0 := eq94 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq94 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807
  have eq1814 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq1813
  have eq1816 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1484 eq1814
    | exact resolve eq1814 eq1484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq1819 : x = (M.op x x) := by
    first
    | (have r₁ := eq1816
       have r₂ := eq27
       grind)
    | exact resolve eq1816 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816
  have eq1826 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1819
       grind)
    | exact superpose eq1819 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1819
       grind)
    | exact resolve eq13 eq1819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1819
  have eq1834 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1826 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826
  have eq1919 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq1834 sF0
       grind)
    | exact superpose eq1834 eq139
    | exact resolve eq139 eq1834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq1834
  have eq1922 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1463 eq1919
    | exact resolve eq1919 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463 eq1919
  have eq1925 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1922
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1922
    | exact resolve eq1922 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1922
  have eq1928 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq1925
    | exact resolve eq1925 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1925
  have eq1997 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1928 eq94
    | (have j0 := eq94 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq94 eq1928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1928
  have eq1998 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1997
  have eq2000 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1484 eq1998
    | exact resolve eq1998 eq1484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484 eq1998
  have eq2003 : False := by grind
  exact eq2003

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation1469 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq78
    | exact resolve eq78 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq79
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79
    | exact resolve eq79 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq88 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) := by
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
  have eq89 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11696 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq80 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11697 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq11696
    | exact resolve eq11696 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11696
  have eq11708 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq11697
       have r₂ := eq28
       grind)
    | exact resolve eq11697 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11697
  have eq11712 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq11708
    | exact resolve eq11708 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11708
  have eq11717 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11712 eq89
    | (have r₁ := eq89
       have r₂ := eq11712
       grind)
    | exact resolve eq89 eq11712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq11712
  have eq11756 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq11717
  have eq11757 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq11756
  have eq12202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11757 eq80
    | exact resolve eq80 eq11757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq11757
  have eq12211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12202
  have eq12214 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12211
       have r₂ := eq28
       grind)
    | exact resolve eq12211 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12211
  have eq12216 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq12214
       grind)
    | exact superpose eq12214 eq52
    | exact resolve eq52 eq12214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq12218 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq12214
       grind)
    | exact superpose eq12214 eq88
    | (have r₁ := eq88
       have r₂ := eq12214
       grind)
    | exact resolve eq88 eq12214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq12214
  have eq12258 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq12218
  have eq12259 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12258
  have eq12273 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq12216
    | exact resolve eq12216 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12216
  have eq12281 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq12259
       grind)
    | exact superpose eq12259 eq49
    | exact resolve eq49 eq12259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq12259
  have eq12297 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq12281
    | exact resolve eq12281 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12281
  have eq12377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12297 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12297
  have eq12378 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12377
  have eq12382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq12378
    | exact resolve eq12378 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12378
  have eq12393 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12382
       have r₂ := eq28
       grind)
    | exact resolve eq12382 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12382
  have eq12397 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq12393
    | exact resolve eq12393 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12393
  have eq12410 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12397 eq12273
    | exact resolve eq12273 eq12397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12273 eq12397
  have eq12445 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12410
  have eq12451 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12445
       have r₂ := eq28
       grind)
    | exact resolve eq12445 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12445
  have eq12454 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq12451 eq30
    | exact resolve eq30 eq12451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12451
  have eq12562 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq12454
    | exact resolve eq12454 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12454
  have eq12563 : x = y := by grind
  clear eq12562
  have eq12580 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq12563
       grind)
    | exact superpose eq12563 eq19
    | exact resolve eq19 eq12563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq12581 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq12563
       grind)
    | exact superpose eq12563 eq25
    | exact resolve eq25 eq12563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12563
  have eq12690 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq12581
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12581
    | exact resolve eq12581 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq12581
  have eq12705 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12690 eq27
    | exact resolve eq27 eq12690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq12690
  have eq12923 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12705 eq71
    | exact resolve eq71 eq12705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq12705
  have eq12977 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12923
       have i₂ := eq12580
       grind)
    | exact superpose eq12580 eq12923
    | exact resolve eq12923 eq12580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12580 eq12923
  have eq12986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12977 eq15
    | exact resolve eq15 eq12977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12977
  have eq13031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq12986
    | exact resolve eq12986 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq12986
  have eq13040 : False := by grind
  exact eq13040

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation1469 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq18
  have eq155 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq157 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (k X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq161 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    grind
  have eq162 : ∀ X0 : G, (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    grind
  clear eq161
  have eq565 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq19 y x
       grind)
    | exact superpose eq19 eq9
    | (have j1 := eq19 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq19 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq19 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq565
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq565
    | exact resolve eq565 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq573 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq572
       have i₂ := eq19 (σ y) (σ x)
       grind)
    | exact superpose eq19 eq572
    | (have j1 := eq19 x y
       grind)
    | (have r₁ := eq572
       have r₂ := eq19 (σ y) (σ x)
       grind)
    | (have r₁ := eq572
       have r₂ := eq19 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq572
       have r₂ := eq19 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq572 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : x = y ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq573
  have eq613 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq574
       grind)
    | exact superpose eq574 eq9
    | exact resolve eq9 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq614 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq613
  have eq615 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq614
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq614
    | exact resolve eq614 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq616 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq615
  have eq617 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq616
  have eq696 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op y X0) (M.op x (k y y))) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq617
       grind)
    | exact superpose eq617 eq16
    | exact resolve eq16 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (k y y) (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq617
       grind)
    | exact superpose eq617 eq16
    | exact resolve eq16 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1303 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op (k y y) (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq20 (σ y) (σ x)
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq20
    | (have j0 := eq20 (σ y) (σ x)
       have j1 := eq697 X0
       grind)
    | (have r₁ := eq20 (σ y) (σ x)
       have r₂ := eq697 X0
       grind)
    | exact resolve eq20 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq1304 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op y X0) (M.op x (k y y))) := by
    intro X0
    first
    | (have i₁ := eq20 (σ y) (σ x)
       have i₂ := eq696 X0
       grind)
    | exact superpose eq696 eq20
    | (have j0 := eq20 (σ y) (σ x)
       have j1 := eq696 X0
       grind)
    | (have r₁ := eq20 (σ y) (σ x)
       have r₂ := eq696 X0
       grind)
    | exact resolve eq20 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq1321 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op y X0) (M.op x (k y y))) := by
    intro X0
    first
    | (have j0 := eq1304 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304
  have eq1322 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op x (k y y))) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1321 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1323 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (k y y) (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have j0 := eq1303 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303
  have eq1324 : ∀ X0 : G, x = (M.op (k y y) (M.op X0 (M.op X0 x))) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1421 : y = (M.op (k y y) (M.op x (k y y))) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1322
  have eq1508 : x = (M.op (k y y) (M.op x (k x x))) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
  have eq1515 : ∀ X1 : G, (k y y) = (M.op x (M.op X1 (M.op X1 (k y y)))) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq16 (k y y) (M.op x (M.op x x)) X1
       have i₂ := eq1324 x
       grind)
    | exact superpose eq1324 eq16
    | exact resolve eq16 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq1807 : y = (M.op (k y y) (M.op x (k y y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq155 y x
       have i₂ := eq617
       grind)
    | exact superpose eq617 eq155
    | exact resolve eq155 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1822 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op (k y y) (M.op x (k y y))) := by
    first
    | exact superpose eq1421 eq1807
    | exact resolve eq1807 eq1421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421 eq1807
  have eq1832 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op (k y y) (M.op x (k y y))) := by
    first
    | (have i₁ := eq572
       have i₂ := eq1822
       grind)
    | exact superpose eq1822 eq572
    | (have r₁ := eq572
       have r₂ := eq1822
       grind)
    | exact resolve eq572 eq1822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1822
  have eq1838 : (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op (k y y) (M.op x (k y y))) := by grind
  clear eq1832
  have eq1929 : y = (M.op (k y y) (M.op x (k y y))) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op (k y y) (M.op x (k y y))) := by
    first
    | (have i₁ := eq155 y x
       have i₂ := eq1838
       grind)
    | exact superpose eq1838 eq155
    | exact resolve eq155 eq1838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838
  have eq1935 : y = (M.op (k y y) (M.op x (k y y))) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1929
  have eq2490 : x = (M.op (k y y) (M.op x (k x x))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq157 x y
       have i₂ := eq617
       grind)
    | exact superpose eq617 eq157
    | exact resolve eq157 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq617
  have eq2526 : x = (M.op (k y y) (M.op x (k x x))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1508 eq2490
    | exact resolve eq2490 eq1508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1508 eq2490
  have eq2540 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y y) = (M.op x (M.op X0 (M.op X0 (k y y)))) := by
    intro X0
    first
    | (have i₁ := eq16 (k y y) (M.op x (k x x)) X0
       have i₂ := eq2526
       grind)
    | exact superpose eq2526 eq16
    | exact resolve eq16 eq2526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526
  have eq2621 : ∀ X0 : G, (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (k y y) = (M.op x (M.op X0 (M.op X0 (k y y)))) := by
    intro X0
    first
    | (have i₁ := eq572
       have i₂ := eq2540 X0
       grind)
    | exact superpose eq2540 eq572
    | (have j1 := eq2540 X0
       grind)
    | (have r₁ := eq572
       have r₂ := eq2540 X0
       grind)
    | exact resolve eq572 eq2540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq2628 : ∀ X0 : G, (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (k y y) = (M.op x (M.op X0 (M.op X0 (k y y)))) := by
    intro X0
    first
    | (have j0 := eq2621 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2621
  have eq2708 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (σ (k y y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k y y) = (M.op x (M.op X0 (M.op X0 (k y y)))) := by
    intro X0
    first
    | (have i₁ := eq9
       have i₂ := eq2628 X0
       grind)
    | exact superpose eq2628 eq9
    | (have j1 := eq2628 X0
       grind)
    | exact resolve eq9 eq2628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2628
  have eq2719 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k y y) = (M.op x (M.op X0 (M.op X0 (k y y)))) := by
    intro X0
    first
    | (have i₁ := eq2708 X0
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq2708
    | (have j0 := eq2708 X0
       grind)
    | exact resolve eq2708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2708
  have eq2720 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k y y) = (M.op x (M.op X0 (M.op X0 (k y y)))) := by
    intro X0
    first
    | exact superpose eq1515 eq2719
    | (have j0 := eq2719 X0
       have j1 := eq1515 X0
       grind)
    | exact resolve eq2719 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515 eq2719
  have eq2721 : ∀ X0 : G, (k y y) = (M.op x (M.op X0 (M.op X0 (k y y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq2720 X0
       have j1 := eq2540 X0
       grind)
    | (have r₁ := eq2720 X0
       have r₂ := eq2540 X0
       grind)
    | exact resolve eq2720 eq2540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540 eq2720
  have eq2796 : (k y y) = (M.op x (M.op (k y y) (k (k y y) (k y y)))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2721
  have eq3086 : (M.op (k y y) (k (k y y) (k y y))) = (M.op (k (M.op (k y y) (k (k y y) (k y y))) (M.op (k y y) (k (k y y) (k y y)))) (M.op x (k y y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq155 (M.op (k y y) (k (k y y) (k y y))) x
       have i₂ := eq2796
       grind)
    | exact superpose eq2796 eq155
    | exact resolve eq155 eq2796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq3091 : (M.op (k y y) (M.op x (k y y))) = (M.op (k y y) (k (k y y) (k y y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3086
       have i₂ := eq162 (k y y)
       grind)
    | exact superpose eq162 eq3086
    | exact resolve eq3086 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq3086
  have eq3093 : y = (M.op (k y y) (k (k y y) (k y y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1935 eq3091
    | exact resolve eq3091 eq1935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935 eq3091
  have eq3242 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2796
       have i₂ := eq3093
       grind)
    | exact superpose eq3093 eq2796
    | exact resolve eq2796 eq3093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3249 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3242
  have eq3256 : (k y y) ≠ (k y y) ∨ (k y x) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq20 y x
       have i₂ := eq3249
       grind)
    | exact superpose eq3249 eq20
    | (have j0 := eq20 y x
       grind)
    | (have r₁ := eq20 y x
       have r₂ := eq3249
       grind)
    | exact resolve eq20 eq3249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3249
  have eq3259 : (k y y) ≠ (k y y) ∨ (k y x) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq3256
  have eq3260 : (k y x) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq3259
  have eq3280 : (k y x) = (M.op x (M.op (k y x) (k (k y x) (k y x)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2796
       have i₂ := eq3260
       grind)
    | exact superpose eq3260 eq2796
    | exact resolve eq2796 eq3260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2796
  have eq3285 : y = (M.op (k y x) (k (k y x) (k y x))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3093
       have i₂ := eq3260
       grind)
    | exact superpose eq3260 eq3093
    | exact resolve eq3093 eq3260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3093
  have eq3287 : (σ (k y x)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq3260
       grind)
    | exact superpose eq3260 eq10
    | exact resolve eq10 eq3260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3260
  have eq3290 : y = (M.op (k y x) (k (k y x) (k y x))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3285
  have eq3295 : (k y x) = (M.op x (M.op (k y x) (k (k y x) (k y x)))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3280
  have eq3313 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3287
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq3287
    | exact resolve eq3287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3287
  have eq3315 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3290 eq3295
    | exact resolve eq3295 eq3290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3290 eq3295
  have eq3326 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9
       have i₂ := eq3315
       grind)
    | exact superpose eq3315 eq9
    | exact resolve eq9 eq3315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3315
  have eq3342 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3326
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq3326
    | exact resolve eq3326 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326
  have eq3838 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3342
       have i₂ := eq19 (σ y) (σ x)
       grind)
    | exact superpose eq19 eq3342
    | (have j1 := eq19 (σ x) (σ y)
       grind)
    | (have r₁ := eq3342
       have r₂ := eq19 (σ y) (σ x)
       grind)
    | (have r₁ := eq3342
       have r₂ := eq19 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq3342
       have r₂ := eq19 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq3342 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3839 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq3838
  have eq3840 : (σ x) = (σ y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq3839
  have eq3847 : (σ x) = (σ y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3313 eq3840
    | exact resolve eq3840 eq3313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3313 eq3840
  have eq3861 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq3847
       have r₂ := eq3342
       grind)
    | exact resolve eq3847 eq3342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342 eq3847
  have eq3869 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq3861
       grind)
    | exact superpose eq3861 eq15
    | exact resolve eq15 eq3861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3861
  have eq3935 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3869
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq3869
    | exact resolve eq3869 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3869
  have eq3936 : x = y := by grind
  clear eq3935
  have eq3939 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq3936
       grind)
    | exact superpose eq3936 eq9
    | exact resolve eq9 eq3936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3936
  have eq3940 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq3939
  have eq3941 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3940
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq3940
    | exact resolve eq3940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3940
  have eq3942 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq3941
  have eq3943 : False := by grind
  exact eq3943

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxy_pxx_pyx_Equation1469 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq32 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq34
  have eq46 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 x y X0
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 y X0 x
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ y) X0 (σ x)
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ x) (σ y) X0
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq104 : ∀ X1 : G, (M.op x y) = (M.op x (M.op X1 (M.op X1 (M.op x y)))) := by
    intro X1
    first
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X1 (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X1
    first
    | exact superpose eq69 eq9
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq188 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq80
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq80 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq188
    | exact resolve eq188 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq194 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq190
    | exact resolve eq190 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq370 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq104 eq64
    | exact resolve eq64 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq372 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq111 eq64
    | exact resolve eq64 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq111
  have eq561 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x y) X1) (M.op X0 (M.op x (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq370 eq9
    | exact resolve eq9 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq600 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq372 eq9
    | exact resolve eq9 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq695 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq65 eq561
    | exact resolve eq561 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq736 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq68 eq600
    | exact resolve eq600 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq3332 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq194
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq194
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq194 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq3352 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3332
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3332
    | exact resolve eq3332 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3332
  have eq3355 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq3352
    | exact resolve eq3352 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352
  have eq3356 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq3355
       have r₂ := eq28
       grind)
    | exact resolve eq3355 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355
  have eq3357 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3356
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3356
    | exact resolve eq3356 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3356
  have eq3359 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3357 eq68
    | exact resolve eq68 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq3364 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3357 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3357
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3357
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3357
       grind)
    | exact resolve eq13 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357
  have eq3378 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq3364
  have eq3381 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq3378
       have r₂ := eq27
       grind)
    | exact resolve eq3378 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3378
  have eq3384 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq80 eq3381
    | exact resolve eq3381 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq3381
  have eq3386 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3359 eq736
    | exact resolve eq736 eq3359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq3359
  have eq3547 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3384
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq3384
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq3384 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3384
  have eq3569 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y x) := by grind
  clear eq3547
  have eq3579 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq3569
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3569
    | exact resolve eq3569 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3569
  have eq3583 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq21 eq3579
    | exact resolve eq3579 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579
  have eq3586 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3583
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3583
    | exact resolve eq3583 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3583
  have eq3587 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3586
  have eq3595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3587 eq3386
    | exact resolve eq3386 eq3587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386 eq3587
  have eq3613 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3595
  have eq3617 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq3613
       have r₂ := eq28
       grind)
    | exact resolve eq3613 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3613
  have eq3628 : y = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq65 x
       have i₂ := eq3617
       grind)
    | exact superpose eq3617 eq65
    | exact resolve eq65 eq3617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq3630 : x = (M.op (M.op x y) (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq3617
       grind)
    | exact superpose eq3617 eq63
    | exact resolve eq63 eq3617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq3631 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op X0 y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq3617
       grind)
    | exact superpose eq3617 eq9
    | exact resolve eq9 eq3617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3617
  have eq3654 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3628 eq695
    | exact resolve eq695 eq3628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq3628
  have eq4063 : y = (M.op (M.op x y) (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3631 y
       have i₂ := eq3654
       grind)
    | exact superpose eq3654 eq3631
    | exact resolve eq3631 eq3654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631 eq3654
  have eq4086 : y = (M.op (M.op x y) (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq4063
  have eq4091 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4086 eq3630
    | exact resolve eq3630 eq4086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3630 eq4086
  have eq4109 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq4091
  have eq4116 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq4109 eq47
    | exact resolve eq47 eq4109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq4109
  have eq4153 : x = y ∨ x = y := by
    first
    | exact superpose eq46 eq4116
    | exact resolve eq4116 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq4116
  have eq4154 : x = y := by grind
  clear eq4153
  have eq4158 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq4154
       grind)
    | exact superpose eq4154 eq19
    | exact resolve eq19 eq4154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4159 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq4154
       grind)
    | exact superpose eq4154 eq25
    | exact resolve eq25 eq4154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4154
  have eq4523 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4159
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4159
    | exact resolve eq4159 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4159
  have eq4616 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4523 eq27
    | exact resolve eq27 eq4523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4523
  have eq5070 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq4158
       grind)
    | exact superpose eq4158 eq35
    | exact resolve eq35 eq4158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq4158
  have eq5087 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5070
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5070
    | exact resolve eq5070 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq5070
  have eq5136 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4616 eq5087
    | exact resolve eq5087 eq4616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4616 eq5087
  have eq5145 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq5136
    | exact resolve eq5136 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq5136
  have eq5149 : False := by grind
  exact eq5149

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxy_pxx_pyx_Equation1469 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq22 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq45
  have eq49 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq52 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq49
  have eq53 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq52
  have eq54 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq16
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq92 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq92
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq92
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq99
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq22 eq105
    | exact resolve eq105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq121 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq39
    | (have j0 := eq39 (M.op x y)
       grind)
    | exact resolve eq39 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq124 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by grind
  clear eq121
  have eq125 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq124
  have eq219 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X1 (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq389 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1 (σ X0)
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq14
    | exact resolve eq14 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq14
    | exact resolve eq14 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op X1 (M.op X1 (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X0) x
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq56
    | exact resolve eq56 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq554 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq56 X0 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq4526 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq219 eq554
    | exact resolve eq554 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq12600 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq12601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq28 eq12600
    | exact resolve eq12600 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12600
  have eq12612 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq12601
       have r₂ := eq29
       grind)
    | exact resolve eq12601 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12601
  have eq12618 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq12612 eq72
    | exact resolve eq72 eq12612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12612
  have eq12690 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq31 eq12618
    | exact resolve eq12618 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12618
  have eq12691 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12690
  have eq12712 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq12691
       grind)
    | exact superpose eq12691 eq54
    | exact resolve eq54 eq12691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq12725 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq389 x X0
       have i₂ := eq12691
       grind)
    | exact superpose eq12691 eq389
    | exact resolve eq389 eq12691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq12691
  have eq12768 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12725 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq12725
    | (have j0 := eq12725 X0
       grind)
    | exact resolve eq12725 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12725
  have eq12772 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12712
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq12712
    | exact resolve eq12712 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12712
  have eq12788 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12768 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12768
    | (have j0 := eq12768 X0
       grind)
    | exact resolve eq12768 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12768
  have eq12793 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28 eq12788
    | (have j0 := eq12788 X0
       grind)
    | exact resolve eq12788 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12788
  have eq12796 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12772 eq125
    | exact resolve eq125 eq12772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq12823 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X0 (σ (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq12772 eq390
    | exact resolve eq390 eq12772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq12825 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (M.op X0 (M.op X0 (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq12772 eq547
    | exact resolve eq547 eq12772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq12772
  have eq12846 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (M.op X0 (M.op X0 (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12825 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12825
    | (have j0 := eq12825 X0
       grind)
    | exact resolve eq12825 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12825
  have eq12848 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X0 (σ (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22 eq12823
    | (have j0 := eq12823 X0
       grind)
    | exact resolve eq12823 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12823
  have eq12857 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12796
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12796
    | exact resolve eq12796 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12796
  have eq12859 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (M.op X0 (M.op X0 (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22 eq12846
    | (have j0 := eq12846 X0
       grind)
    | exact resolve eq12846 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12846
  have eq12861 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X0 (σ (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12848 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12848
    | (have j0 := eq12848 X0
       grind)
    | exact resolve eq12848 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12848
  have eq14039 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12793 eq4526
    | exact resolve eq4526 eq12793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4526 eq12793
  have eq21740 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14039 eq12859
    | exact resolve eq12859 eq14039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12859 eq14039
  have eq21782 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21740
  have eq22104 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21782 eq219
    | exact resolve eq219 eq21782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq21782
  have eq22455 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12857 eq12861
    | exact resolve eq12861 eq12857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12857 eq12861
  have eq22500 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22455
  have eq22511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22500 eq22104
    | exact resolve eq22104 eq22500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22104 eq22500
  have eq22541 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22511
  have eq22546 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq22541
       have r₂ := eq29
       grind)
    | exact resolve eq22541 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22541
  have eq22655 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq22546 eq31
    | exact resolve eq31 eq22546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq22546
  have eq22766 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq22655
    | exact resolve eq22655 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq22655
  have eq22767 : x = y := by grind
  clear eq22766
  have eq22786 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq22767
       grind)
    | exact superpose eq22767 eq20
    | exact resolve eq20 eq22767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq22787 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq22767
       grind)
    | exact superpose eq22767 eq26
    | exact resolve eq26 eq22767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq22767
  have eq22895 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq22787
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22787
    | exact resolve eq22787 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq22787
  have eq22910 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22895 eq28
    | exact resolve eq28 eq22895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq22895
  have eq23178 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq22910 eq72
    | exact resolve eq72 eq22910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq22910
  have eq23264 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq23178
       have i₂ := eq22786
       grind)
    | exact superpose eq22786 eq23178
    | exact resolve eq23178 eq22786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22786 eq23178
  have eq23275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23264 eq15
    | exact resolve eq15 eq23264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23264
  have eq23322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq23275
    | exact resolve eq23275 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23275
  have eq23331 : False := by grind
  exact eq23331

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_pxx_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq50 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 X1 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq70 sF2
       grind)
    | exact superpose eq70 eq49
    | exact resolve eq49 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq75 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq74
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq74
    | exact resolve eq74 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq74
  have eq81 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq81 y x
       grind)
    | exact superpose eq81 eq102
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq102 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
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
  have eq1040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq119 eq81
    | (have j0 := eq81 (σ x) (σ y)
       grind)
    | exact resolve eq81 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq119
  have eq1041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq1040
    | exact resolve eq1040 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1044 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1041
       have r₂ := eq27
       grind)
    | exact resolve eq1041 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1046 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq1044
    | exact resolve eq1044 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1048 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1046 eq54
    | exact resolve eq54 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1049 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1046 eq51
    | exact resolve eq51 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1046
  have eq1164 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f1164_13 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
      intro X0
      grind
    have f1164_14 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
      intro X0
      grind
    have f1164_22 : (σ y) ≠ (σ x) := by grind
    have f1164_24 : (M.op x y) ≠ (M.op y x) := by grind
    have f1164_26 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
      intro X0
      first
      | (have j0 := f1164_14 X0
         grind)
      | (have r₁ := f1164_14 X0
         have r₂ := f1164_24
         grind)
      | exact resolve f1164_14 f1164_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1164_27 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
      intro X0
      first
      | (have j0 := f1164_13 X0
         grind)
      | (have r₁ := f1164_13 X0
         have r₂ := f1164_24
         grind)
      | exact resolve f1164_13 f1164_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1164_97 : (σ y) = (σ x) := by
      first
      | (have i₁ := f1164_26 x
         have i₂ := f1164_27 x
         grind)
      | exact superpose f1164_27 f1164_26
      | exact resolve f1164_26 f1164_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1164_102 : False := by
      first
      | (have r₁ := f1164_97
         have r₂ := f1164_22
         grind)
      | exact resolve f1164_97 f1164_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f1164_102
  clear eq1048 eq1049
  have eq1180 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq1164
  have eq1182 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq1180
       grind)
    | exact superpose eq1180 eq53
    | exact resolve eq53 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1183 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq50 X0 y
       have i₂ := eq1180
       grind)
    | exact superpose eq1180 eq50
    | exact resolve eq50 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1180
  have eq1484 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f1484_13 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) := by
      intro X0
      grind
    have f1484_14 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) := by
      intro X0
      grind
    have f1484_22 : y ≠ x := by grind
    have f1484_24 : (σ x) ≠ (σ y) := by grind
    have f1484_26 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
      intro X0
      first
      | (have j0 := f1484_14 X0
         grind)
      | (have r₁ := f1484_14 X0
         have r₂ := f1484_24
         grind)
      | exact resolve f1484_14 f1484_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1484_27 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
      intro X0
      first
      | (have j0 := f1484_13 X0
         grind)
      | (have r₁ := f1484_13 X0
         have r₂ := f1484_24
         grind)
      | exact resolve f1484_13 f1484_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1484_57 : y = x := by
      first
      | (have i₁ := f1484_26 x
         have i₂ := f1484_27 x
         grind)
      | exact superpose f1484_27 f1484_26
      | exact resolve f1484_26 f1484_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1484_61 : False := by
      first
      | (have r₁ := f1484_57
         have r₂ := f1484_22
         grind)
      | exact resolve f1484_57 f1484_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f1484_61
  clear eq1182 eq1183
  have eq1506 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1484
  have eq1509 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1506 eq29
    | exact resolve eq29 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1506
  have eq1532 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq1509
    | exact resolve eq1509 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1509
  have eq1533 : x = y := by grind
  clear eq1532
  have eq1536 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1533
       grind)
    | exact superpose eq1533 eq18
    | exact resolve eq18 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1537 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1533
       grind)
    | exact superpose eq1533 eq24
    | exact resolve eq24 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1533
  have eq1561 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1537
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1537
    | exact resolve eq1537 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1537
  have eq1564 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1561 eq26
    | exact resolve eq26 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1561
  have eq1614 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1564 eq75
    | exact resolve eq75 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1564
  have eq1633 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1614
       have i₂ := eq1536
       grind)
    | exact superpose eq1536 eq1614
    | exact resolve eq1614 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536 eq1614
  have eq1636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1633 eq15
    | exact resolve eq15 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633
  have eq1655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1636
    | exact resolve eq1636 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1636
  have eq1659 : False := by grind
  exact eq1659

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_pyx_pxy_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq51 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 X1 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) X3) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X1 (M.op X2 X0)) X3 X4 (M.op X0 x)
       have i₂ := eq14 X0 x X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 (M.op X0 x) x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X2) ≠ X0 ∨ (M.op X2 (M.op X0 (M.op X1 X0))) = (k X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 (M.op X1 X0))
       have i₂ := eq14 X0 (M.op X1 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X0 (M.op X1 X0))
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq70 (σ X0)
       grind)
    | exact superpose eq70 eq10
    | exact resolve eq10 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq43
    | exact resolve eq43 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq76 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq70 sF2
       grind)
    | exact superpose eq70 eq73
    | exact resolve eq73 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq72
    | exact resolve eq72 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq81 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq81
    | (have j0 := eq81 (σ X0) (σ X1)
       grind)
    | exact resolve eq81 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq44
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq44 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103 eq81
    | (have j0 := eq81 (σ x) (σ y)
       grind)
    | exact resolve eq81 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq106
    | exact resolve eq106 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq110 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq107
       have r₂ := eq27
       grind)
    | exact resolve eq107 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq112 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq110
    | exact resolve eq110 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq114 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq112 eq27
    | exact resolve eq27 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : x ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ (k x y) = (M.op y x) := by
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
  have eq116 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq132 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq128
       have i₂ := eq70 sF3
       grind)
    | exact superpose eq70 eq128
    | exact resolve eq128 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq134 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq132
       have i₂ := eq70 y
       grind)
    | exact superpose eq70 eq132
    | exact resolve eq132 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq132
  have eq142 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq171 : (σ (k (M.op y y) x)) = (k (M.op (σ y) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq39 (M.op y y)
       have i₂ := eq134
       grind)
    | exact superpose eq134 eq39
    | exact resolve eq39 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq81 (σ X0) sF2
       grind)
    | exact superpose eq81 eq39
    | (have j1 := eq81 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq81
  have eq196 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq142 eq16
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (σ (k (M.op y y) (M.op x y))) = (k (M.op (σ y) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq41 (M.op y y)
       have i₂ := eq134
       grind)
    | exact superpose eq134 eq41
    | exact resolve eq41 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq275 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq112 eq54
    | exact resolve eq54 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq364 eq51
    | exact resolve eq51 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op (M.op X0 (σ x)) X1) (M.op X2 (σ y))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq364 eq14
    | exact resolve eq14 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op X1 (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq382 eq14
    | exact resolve eq14 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X1) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq403 eq14
    | exact resolve eq14 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq510 : ∀ X0 X3 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X3 (σ y))) ∨ x = (M.op x y) := by
    intro X0 X3
    first
    | (have i₁ := eq387 X0 (M.op x (M.op X3 X0)) x
       have i₂ := eq14 X0 sF2 x X3
       grind)
    | exact superpose eq14 eq387
    | exact resolve eq387 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq543 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq510
    | (have j0 := eq510 X0 (σ x)
       grind)
    | exact resolve eq510 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq577 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X1) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq543 eq452
    | exact resolve eq452 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq592 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X1) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq577 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq827 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1028 : ∀ X0 X2 X3 X4 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) X3) (M.op X4 (M.op X2 (M.op x y)))) := by
    intro X0 X2 X3 X4
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1073 : ∀ X0 X1 X3 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ y) (M.op X3 X1)) ∨ x = (M.op x y) := by
    intro X0 X1 X3
    first
    | exact superpose eq364 eq55
    | exact resolve eq55 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1127 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X3 X2 X4 (M.op (M.op X0 (M.op X1 X2)) x)
       have i₂ := eq55 X2 X0 X1 x X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1439 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq112 eq116
    | (have r₁ := eq116
       have r₂ := eq112
       grind)
    | exact resolve eq116 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq1440 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1439
  have eq1780 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (σ (k X0 X1)) (M.op X2 (M.op X3 (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (σ X0) (σ X1) X2 X3
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq14
    | (have j1 := eq87 X0 X1
       grind)
    | exact resolve eq14 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1785 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (M.op (σ (k X0 X1)) X2) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (σ X1) (σ X0) X2
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq56
    | (have j1 := eq87 X0 X1
       grind)
    | exact resolve eq56 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq1937 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) = (k X1 (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 (M.op X0 X1) X2 X1
       have i₂ := eq56 X1 X0 (M.op X2 (M.op X0 X1))
       grind)
    | exact superpose eq56 eq69
    | (have j0 := eq69 (M.op X0 X1) X2 X1
       grind)
    | (have r₁ := eq69 (M.op X1 X0) X1 X0
       have r₂ := eq56 X0 X1 (M.op X1 (M.op X1 X0))
       grind)
    | exact resolve eq69 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1941 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 (M.op X1 X2)) ∨ (M.op (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2))))) = (k (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 (M.op X0 (M.op X1 X2)) X3 (M.op X4 X2)
       have i₂ := eq55 X2 X0 X1 (M.op X3 (M.op X0 (M.op X1 X2))) X4
       grind)
    | exact superpose eq55 eq69
    | (have j0 := eq69 (M.op X0 (M.op X1 X2)) X3 (M.op X4 X2)
       grind)
    | (have r₁ := eq69 (M.op X1 (M.op X2 X0)) X1 (M.op X4 X0)
       have r₂ := eq55 X0 X1 X2 (M.op X1 (M.op X1 (M.op X2 X0))) X4
       grind)
    | exact resolve eq69 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq69
  have eq1968 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2))))) = (k (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq1941 X0 X1 X2 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1941
  have eq1972 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) = (k X1 (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1937 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq3161 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq592 eq51
    | exact resolve eq51 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq4226 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X2 (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 y X2 X0
       have i₂ := eq827 X0 X1
       grind)
    | (have i₁ := eq52 x y x X0
       have i₂ := eq827 X0 X1
       grind)
    | exact superpose eq827 eq52
    | exact resolve eq52 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4305 : ∀ X0 X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (M.op X2 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq828 eq52
    | exact resolve eq52 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4370 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq77 (M.op y y)
       have i₂ := eq134
       grind)
    | exact superpose eq134 eq77
    | exact resolve eq77 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4389 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X2 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1 X2
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq14
    | exact resolve eq14 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4394 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X0) x
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq56
    | exact resolve eq56 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4398 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 (σ X0))) = (M.op (σ y) (σ (M.op X0 X0))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1073 (σ X0) (σ X0) X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq1073
    | exact resolve eq1073 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq4408 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y y) (M.op x y))) := by
    first
    | (have i₁ := eq4370
       have i₂ := eq827 (M.op y y) y
       grind)
    | exact superpose eq827 eq4370
    | exact resolve eq4370 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq4370
  have eq4410 : (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op y y) (M.op x y))) := by
    first
    | exact superpose eq828 eq4408
    | exact resolve eq4408 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4408
  have eq7525 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op X0 (σ (M.op y (M.op x y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq53 eq4398
    | exact resolve eq4398 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4398
  have eq7640 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op X0 (σ (M.op y (M.op x y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7525 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7525
    | (have j0 := eq7525 X0
       grind)
    | exact resolve eq7525 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7525
  have eq7753 : ∀ X0 X1 : G, (M.op X0 (σ (M.op y (M.op x y)))) = (M.op X0 (M.op X1 (M.op (σ y) (σ y)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq7640 eq52
    | exact resolve eq52 eq7640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq7754 : ∀ X0 : G, (σ (M.op y (M.op x y))) = (M.op (M.op (σ (M.op y (M.op x y))) X0) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7640 eq14
    | exact resolve eq14 eq7640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7640
  have eq7802 : ∀ X0 : G, (σ (M.op y (M.op x y))) = (M.op (M.op (σ (M.op y (M.op x y))) X0) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq828 eq7754
    | exact resolve eq7754 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7754
  have eq7803 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) = (M.op X0 (σ (M.op y (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq828 eq7753
    | exact resolve eq7753 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7753
  have eq7977 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ (M.op y (M.op x y))))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7803 eq3161
    | exact resolve eq3161 eq7803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3161 eq7803
  have eq8153 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ (M.op y (M.op x y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7977 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7977
  have eq9409 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X1 (σ (k X0 x)))) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq181 eq51
    | (have j1 := eq181 X0
       grind)
    | exact resolve eq51 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq181
  have eq11533 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq142 eq1780
    | (have j0 := eq1780 (M.op x y) y x x
       grind)
    | exact resolve eq1780 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780
  have eq11651 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq20 eq11533
    | (have j0 := eq11533 X0 X1
       grind)
    | exact resolve eq11533 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11533
  have eq11675 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 (M.op X1 (σ (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq11651 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11651
    | (have j0 := eq11651 X0 X1
       grind)
    | exact resolve eq11651 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11651
  have eq11697 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 (M.op X1 (σ (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq20 eq11675
    | (have j0 := eq11675 X0 X1
       grind)
    | exact resolve eq11675 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11675
  have eq12273 : ∀ X0 : G, (k (σ (M.op x y)) (σ y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) X0) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq142 eq1785
    | (have j0 := eq1785 (M.op x y) y x
       grind)
    | exact resolve eq1785 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1785
  have eq12397 : ∀ X0 : G, (k (σ (M.op x y)) (σ y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) X0) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12273 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12273
    | (have j0 := eq12273 X0
       grind)
    | exact resolve eq12273 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12273
  have eq12422 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12397 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12397
    | (have j0 := eq12397 X0
       grind)
    | exact resolve eq12397 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12397
  have eq12444 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq12422
    | (have j0 := eq12422 X0
       grind)
    | exact resolve eq12422 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12422
  have eq14842 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1972 X0 X1 X2
       have i₂ := eq1127 X2 X0 X1 X1 (M.op X0 X1)
       grind)
    | exact superpose eq1127 eq1972
    | exact resolve eq1972 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1972
  have eq15016 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (σ x) (M.op (M.op X0 (σ x)) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq364 eq14842
    | exact resolve eq14842 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15068 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq1028 eq14842
    | exact resolve eq14842 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028 eq14842
  have eq15552 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (σ x) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15016 (M.op x sF3)
       have i₂ := eq56 sF3 x sF2
       grind)
    | exact superpose eq56 eq15016
    | exact resolve eq15016 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq15016
  have eq19825 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) X2)) = (k (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) X2)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1968 X0 X1 X2 X4 X4
       have i₂ := eq1127 X0 X1 X2 (M.op X0 (M.op X1 X2)) X4
       grind)
    | exact superpose eq1127 eq1968
    | exact resolve eq1968 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968
  have eq19830 : (σ (M.op y (M.op x y))) = (M.op (σ (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7802 (σ (M.op y sF0))
       have i₂ := eq77 (M.op y sF0)
       grind)
    | exact superpose eq77 eq7802
    | exact resolve eq7802 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq7802
  have eq20016 : (σ (M.op y (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53 eq19830
    | exact resolve eq19830 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19830
  have eq20018 : (σ (M.op y (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20016
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20016
    | exact resolve eq20016 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20016
  have eq20401 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ y)) = (k (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq19825
    | exact resolve eq19825 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20408 : ∀ X0 : G, (M.op (M.op X0 y) (M.op x y)) = (k (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq275 eq19825
    | exact resolve eq19825 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq19825
  have eq20751 : (M.op y (M.op x y)) = (τ (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20018 eq16
    | exact resolve eq16 eq20018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20018
  have eq20837 : (M.op y (M.op x y)) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq543 eq20751
    | exact resolve eq20751 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq20751
  have eq20858 : (M.op y (M.op x y)) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq20837
  have eq40978 : (k (M.op (σ y) (σ y)) (σ (M.op x y))) = (σ (M.op (M.op y y) (M.op x y))) := by
    first
    | exact superpose eq20408 eq233
    | exact resolve eq233 eq20408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq20408
  have eq43290 : (k (M.op (σ y) (σ y)) (σ (M.op x y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4410 eq40978
    | exact resolve eq40978 eq4410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4410 eq40978
  have eq48273 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1440 eq103
    | exact resolve eq103 eq1440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq48289 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq48273
  have eq48346 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (M.op X2 (M.op (σ y) (σ x))))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq48289 eq1127
    | exact resolve eq1127 eq48289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48289
  have eq48387 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq48346 x x X0
       have i₂ := eq1127 X0 sF3 sF2 x x
       grind)
    | exact superpose eq1127 eq48346
    | exact resolve eq48346 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48346
  have eq48595 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq48387
    | (have j0 := eq48387 (σ x)
       grind)
    | exact resolve eq48387 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48725 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq48387 eq382
    | exact resolve eq382 eq48387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq48387
  have eq48733 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq48725
  have eq48832 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq48595 eq364
    | exact resolve eq364 eq48595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq48595
  have eq48921 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq48832 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48832
  have eq49130 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq112 eq48733
    | exact resolve eq48733 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq48733
  have eq49237 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq49130
  have eq53846 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq48921 eq54
    | exact resolve eq54 eq48921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48921
  have eq58432 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq53846 eq15552
    | exact resolve eq15552 eq53846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15552 eq53846
  have eq58480 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq58432
  have eq74960 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq58480 eq103
    | exact resolve eq103 eq58480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58480
  have eq74982 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq74960
  have eq75001 : (τ (σ (M.op x y))) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq74982 eq20858
    | exact resolve eq20858 eq74982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74982
  have eq75255 : (τ (σ (M.op x y))) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq75001
  have eq75310 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq30 eq75255
    | exact resolve eq75255 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75255
  have eq75482 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq75310 eq49237
    | exact resolve eq49237 eq75310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49237 eq75310
  have eq75631 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y (M.op x y)) := by grind
  clear eq75482
  have eq75644 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have r₁ := eq75631
       have r₂ := eq114
       grind)
    | exact resolve eq75631 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq75631
  have eq75926 : (τ (σ (M.op x y))) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq75644 eq20858
    | exact resolve eq20858 eq75644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20858 eq75644
  have eq76180 : (τ (σ (M.op x y))) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) := by grind
  clear eq75926
  have eq76235 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq30 eq76180
    | exact resolve eq76180 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76180
  have eq76236 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq76235
  have eq76384 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 (M.op X2 (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq76236 eq1127
    | exact resolve eq1127 eq76236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76236
  have eq76504 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4226 eq76384
    | exact resolve eq76384 eq4226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226 eq76384
  have eq80062 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ (M.op y y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq76504 eq8153
    | exact resolve eq8153 eq76504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8153 eq76504
  have eq80283 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ (M.op y y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq80062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80062
  have eq80423 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq80283 X0
       have i₂ := eq134
       grind)
    | exact superpose eq134 eq80283
    | exact resolve eq80283 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80283
  have eq80514 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq828 eq80423
    | exact resolve eq80423 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80423
  have eq92369 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80514 eq20401
    | exact resolve eq20401 eq80514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20401 eq80514
  have eq92387 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq92369
    | exact resolve eq92369 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92369
  have eq92397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92387 eq103
    | exact resolve eq103 eq92387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq92387
  have eq92421 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq92397
  have eq92433 : x = (M.op x y) := by
    first
    | (have r₁ := eq92421
       have r₂ := eq27
       grind)
    | exact resolve eq92421 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92421
  have eq92436 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq92433 eq20
    | exact resolve eq20 eq92433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq92439 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 x)) := by
    intro X0 X1
    first
    | exact superpose eq92433 eq53
    | exact resolve eq53 eq92433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq92442 : x ≠ x ∨ (M.op y x) = (M.op y y) ∨ (k x y) = (M.op y x) := by
    first
    | exact superpose eq92433 eq115
    | (have r₁ := eq115
       have r₂ := eq92433
       grind)
    | exact resolve eq115 eq92433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq92517 : ∀ X0 : G, (M.op x x) = (k x (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq92433 eq15068
    | exact resolve eq15068 eq92433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15068
  have eq92524 : (M.op y x) = (M.op y y) ∨ (k x y) = (M.op y x) := by grind
  clear eq92442
  have eq92586 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq92436
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq92436
    | exact resolve eq92436 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92436
  have eq92608 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq92586 eq26
    | exact resolve eq26 eq92586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq93394 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq4394 (M.op y x) x
       have i₂ := eq92439 x y
       grind)
    | exact superpose eq92439 eq4394
    | exact resolve eq4394 eq92439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4394
  have eq93471 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq93394 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq93394
    | (have j0 := eq93394 X0
       grind)
    | exact resolve eq93394 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93394
  have eq96364 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 (M.op X1 (σ (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq92608 eq11697
    | (have j0 := eq11697 X0 X1
       grind)
    | exact resolve eq11697 eq92608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11697
  have eq96365 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 (M.op X1 (σ (M.op x y))))) := by
    intro X0 X1
    first
    | (have j0 := eq96364 X0 X1
       grind)
    | (have r₁ := eq96364 X0 X1
       have r₂ := eq27
       grind)
    | exact resolve eq96364 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96364
  have eq97121 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq92608 eq12444
    | (have j0 := eq12444 X0
       grind)
    | exact resolve eq12444 eq92608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12444
  have eq97122 : ∀ X0 : G, (k (σ (M.op x y)) (σ y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq97121 X0
       grind)
    | (have r₁ := eq97121 X0
       have r₂ := eq27
       grind)
    | exact resolve eq97121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97121
  have eq97125 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq96365 eq97122
    | exact resolve eq97122 eq96365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97122
  have eq97296 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq92608 eq97125
    | exact resolve eq97125 eq92608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97125
  have eq97325 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) := by
    first
    | exact superpose eq97296 eq196
    | exact resolve eq196 eq97296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq97353 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq92433 eq97325
    | exact resolve eq97325 eq92433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97325
  have eq98553 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (σ (k X0 x)))) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq92586 eq9409
    | (have j0 := eq9409 X0 X1
       grind)
    | exact resolve eq9409 eq92586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9409
  have eq98554 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (σ (k X0 x)))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq92586 eq98553
    | (have j0 := eq98553 X0 X1
       grind)
    | exact resolve eq98553 eq92586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98553
  have eq98573 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (k (M.op (σ y) (σ y)) (σ x)))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq98554 (M.op y y) X0
       have i₂ := eq171
       grind)
    | exact superpose eq171 eq98554
    | (have j0 := eq98554 (M.op y y) x
       grind)
    | exact resolve eq98554 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq98554
  have eq98705 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (k (M.op (σ y) (σ y)) (σ (M.op x y))))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq92586 eq98573
    | exact resolve eq98573 eq92586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98573
  have eq98726 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq43290 eq98705
    | exact resolve eq98705 eq43290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43290 eq98705
  have eq98737 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4305 eq98726
    | exact resolve eq98726 eq4305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4305 eq98726
  have eq98744 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq98737
       have i₂ := eq134
       grind)
    | exact superpose eq134 eq98737
    | exact resolve eq98737 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq98737
  have eq108757 : ∀ X0 : G, (σ (M.op y x)) = (M.op (σ (M.op (M.op y x) (M.op y x))) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq93471 eq4389
    | exact resolve eq4389 eq93471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4389
  have eq108827 : (σ (M.op y x)) = (M.op (σ (M.op (M.op y x) (M.op y x))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq828 eq108757
    | (have j0 := eq108757 (σ x)
       grind)
    | exact resolve eq108757 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108757
  have eq108839 : (σ (M.op y x)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq108827
       have i₂ := eq92439 x y
       grind)
    | exact superpose eq92439 eq108827
    | exact resolve eq108827 eq92439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108827
  have eq108846 : (σ (M.op y x)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq108839
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq108839
    | exact resolve eq108839 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq108839
  have eq198245 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 (M.op (σ y) (σ y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq98744 eq96365
    | exact resolve eq96365 eq98744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96365 eq98744
  have eq198328 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq828 eq198245
    | exact resolve eq198245 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828 eq198245
  have eq198345 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq97296 eq198328
    | exact resolve eq198328 eq97296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97296 eq198328
  have eq249156 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq92524
       have i₂ := eq97353
       grind)
    | exact superpose eq97353 eq92524
    | exact resolve eq92524 eq97353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92524
  have eq249246 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op X1 (M.op X2 (M.op y x)))) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1127 X2 y y X0 X1
       have i₂ := eq249156
       grind)
    | exact superpose eq249156 eq1127
    | exact resolve eq1127 eq249156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249156
  have eq249298 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq249246 X0 x x
       have i₂ := eq1127 x y x X0 x
       grind)
    | exact superpose eq1127 eq249246
    | exact resolve eq249246 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127 eq249246
  have eq249600 : (M.op x y) = (M.op x x) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18
       have i₂ := eq249298 x
       grind)
    | exact superpose eq249298 eq18
    | (have j1 := eq249298 x
       grind)
    | exact resolve eq18 eq249298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249298
  have eq249696 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq92433 eq249600
    | exact resolve eq249600 eq92433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249600
  have eq249847 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ (τ (M.op (σ x) (σ y))))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq93471 X0
       have i₂ := eq249696
       grind)
    | exact superpose eq249696 eq93471
    | exact resolve eq93471 eq249696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93471
  have eq249848 : (M.op (σ y) (M.op (σ x) (σ y))) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq108846
       have i₂ := eq249696
       grind)
    | exact superpose eq249696 eq108846
    | exact resolve eq108846 eq249696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108846 eq249696
  have eq249954 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq249848
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq249848
    | exact resolve eq249848 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249848
  have eq249955 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq249847 X0
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq249847
    | exact resolve eq249847 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249847
  have eq250096 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq249954 eq54
    | exact resolve eq54 eq249954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq250783 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq249954 eq249955
    | exact resolve eq249955 eq249954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249954
  have eq250983 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq249955 eq198345
    | exact resolve eq198345 eq249955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198345 eq249955
  have eq251038 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq250983
  have eq251049 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by grind
  clear eq250783
  have eq252253 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq251049 eq250096
    | exact resolve eq250096 eq251049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250096 eq251049
  have eq252381 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq252253
  have eq252436 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq252381 eq251038
    | exact resolve eq251038 eq252381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251038 eq252381
  have eq252523 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq252436
  have eq252608 : ∀ X0 : G, y = (M.op (M.op y X0) x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq92439 X0 x
       have i₂ := eq252523
       grind)
    | exact superpose eq252523 eq92439
    | exact resolve eq92439 eq252523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253526 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq92439 X0 (M.op y x)
       have i₂ := eq252608 x
       grind)
    | exact superpose eq252608 eq92439
    | exact resolve eq92439 eq252608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92439 eq252608
  have eq259318 : (k x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq92517 (M.op y x)
       have i₂ := eq253526 x
       grind)
    | exact superpose eq253526 eq92517
    | exact resolve eq92517 eq253526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92517 eq253526
  have eq259422 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq259318
       have i₂ := eq97353
       grind)
    | exact superpose eq97353 eq259318
    | exact resolve eq259318 eq97353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97353 eq259318
  have eq259517 : x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq252523
       have i₂ := eq259422
       grind)
    | exact superpose eq259422 eq252523
    | exact resolve eq252523 eq259422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252523 eq259422
  have eq259604 : x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq259517
  have eq259710 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq259604 eq15
    | exact resolve eq15 eq259604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259604
  have eq259931 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq259710
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq259710
    | exact resolve eq259710 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259710
  have eq259949 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq92586 eq259931
    | exact resolve eq259931 eq92586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259931
  have eq259958 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq259949
       have r₂ := eq27
       grind)
    | exact resolve eq259949 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259949
  have eq259976 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq259958 eq29
    | exact resolve eq29 eq259958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq260298 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq259958 eq92608
    | exact resolve eq92608 eq259958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92608 eq259958
  have eq260453 : y = (M.op x y) := by
    first
    | exact superpose eq30 eq259976
    | exact resolve eq259976 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq259976
  have eq260495 : x = y := by
    first
    | exact superpose eq92433 eq260453
    | exact resolve eq260453 eq92433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260453
  have eq260525 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq260495
       grind)
    | exact superpose eq260495 eq18
    | exact resolve eq18 eq260495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq260495
  have eq260993 : x = (M.op x x) := by
    first
    | exact superpose eq92433 eq260525
    | exact resolve eq260525 eq92433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92433 eq260525
  have eq262727 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq260993
       grind)
    | exact superpose eq260993 eq76
    | exact resolve eq76 eq260993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq260993
  have eq262890 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq92586 eq262727
    | exact resolve eq262727 eq92586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262727
  have eq262932 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq260298 eq262890
    | exact resolve eq262890 eq260298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260298 eq262890
  have eq262956 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq262932
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq262932
    | exact resolve eq262932 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq262932
  have eq262974 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq92586 eq262956
    | exact resolve eq262956 eq92586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92586 eq262956
  have eq262987 : False := by grind
  exact eq262987
