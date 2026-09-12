import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_pxx_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq125 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq125 (σ X0)
       grind)
    | exact superpose eq125 eq15
    | exact resolve eq15 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq131 X0
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq131
    | exact resolve eq131 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq131
  have eq165 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq142 X0
       grind)
    | exact superpose eq142 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq689 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq672 X0 X1
       have i₂ := eq142 X1
       grind)
    | exact superpose eq142 eq672
    | (have j0 := eq672 X0 X1
       grind)
    | exact resolve eq672 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq5070 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq689 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq689
    | exact resolve eq689 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq5178 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5070 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq5070
    | (have j0 := eq5070 X0 X1
       grind)
    | exact resolve eq5070 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5070
  have eq5196 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5178 X0 X1
       have j1 := eq165 X1 X0
       grind)
    | (have r₁ := eq5178 X1 X0
       have r₂ := eq165 X0 X1
       grind)
    | (have r₁ := eq5178 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq165 X0 X1
       grind)
    | exact resolve eq5178 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq5178
  have eq5208 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5196 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5196
    | exact resolve eq5196 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5232 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq5196 (σ X0) X1
       grind)
    | exact superpose eq5196 eq15
    | (have j1 := eq5196 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq5196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5196
  have eq5311 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq5208 (τ X1) X0
       grind)
    | exact superpose eq5208 eq19
    | (have j1 := eq5208 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq5208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq5208
  have eq5488 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5311 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5311
    | exact resolve eq5311 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5311
  have eq5575 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5488 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5488
    | (have j0 := eq5488 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq5488 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5488
  have eq5880 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5232 x y
       grind)
    | exact superpose eq5232 eq16
    | (have j1 := eq5232 x y
       grind)
    | exact resolve eq16 eq5232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5232
  have eq5961 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5880
       have i₂ := eq5575 y x
       grind)
    | exact superpose eq5575 eq5880
    | (have j1 := eq5575 (σ x) (σ y)
       grind)
    | (have r₁ := eq5880
       have r₂ := eq5575 y x
       grind)
    | (have r₁ := eq5880
       have r₂ := eq5575 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5880
       have r₂ := eq5575 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5880 eq5575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5575 eq5880
  have eq5962 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5961
  have eq5965 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5962
       grind)
    | exact superpose eq5962 eq16
    | exact resolve eq16 eq5962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5962
  have eq5966 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5965
       have r₂ := eq142 x
       grind)
    | exact resolve eq5965 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5965
  have eq5967 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5966
       grind)
    | exact superpose eq5966 eq16
    | exact resolve eq16 eq5966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5968 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5966
       grind)
    | exact superpose eq5966 eq10
    | exact resolve eq10 eq5966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5966
  have eq6036 : x = y := by
    first
    | (have i₁ := eq5968
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5968
    | exact resolve eq5968 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5968
  have eq6037 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5967
       have i₂ := eq142 x
       grind)
    | exact superpose eq142 eq5967
    | exact resolve eq5967 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq5967
  have eq6038 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6037
       have i₂ := eq6036
       grind)
    | exact superpose eq6036 eq6037
    | exact resolve eq6037 eq6036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6036 eq6037
  have eq6039 : False := by grind
  exact eq6039

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_x_pxy_y_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
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
  clear eq24 eq35
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X2)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X0 (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X1) X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq93 x y
       grind)
    | exact superpose eq93 eq44
    | (have j1 := eq93 x x
       grind)
    | exact resolve eq44 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq105
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq202 : (M.op x y) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq441 : (M.op x y) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq50 eq55
    | exact resolve eq55 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq460 : x = (M.op (M.op x y) (M.op x (M.op x y))) := by
    first
    | exact superpose eq441 eq55
    | exact resolve eq55 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq586 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op X0 X1) X0 (M.op (M.op X0 (M.op X1 x)) x)
       have i₂ := eq52 X0 X1 x x
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq55
  have eq843 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq117 eq93
    | (have j0 := eq93 (σ x) x
       grind)
    | exact resolve eq93 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq844 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq843
    | exact resolve eq843 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq847 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq844
       have r₂ := eq27
       grind)
    | exact resolve eq844 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq852 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq847 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq847
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq847
       grind)
    | exact resolve eq13 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq860 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq852
  have eq888 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq860 eq49
    | exact resolve eq49 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq860
  have eq892 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq888
    | exact resolve eq888 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq888
  have eq895 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq93 x x
       have i₂ := eq892
       grind)
    | exact superpose eq892 eq93
    | (have j0 := eq93 x x
       grind)
    | exact resolve eq93 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq896 : x = (M.op x x) := by grind
  clear eq895
  have eq899 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq204 x
       have i₂ := eq896
       grind)
    | exact superpose eq896 eq204
    | exact resolve eq204 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq902 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq896
       grind)
    | exact superpose eq896 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq896
       grind)
    | exact resolve eq13 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq912 : x = (k x x) := by grind
  clear eq902
  have eq916 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq912
       grind)
    | exact superpose eq912 eq43
    | exact resolve eq43 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq912
  have eq920 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq916
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq916
    | exact resolve eq916 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq923 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq920 eq93
    | (have j0 := eq93 (σ x) x
       grind)
    | exact resolve eq93 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq920
  have eq924 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq923
  have eq927 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq924 eq208
    | exact resolve eq208 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq943 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq899 eq56
    | exact resolve eq56 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq957 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq943
       have i₂ := eq896
       grind)
    | exact superpose eq896 eq943
    | exact resolve eq943 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq962 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq957 eq460
    | exact resolve eq460 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460 eq957
  have eq980 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq962 eq202
    | exact resolve eq202 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq962
  have eq993 : x = (M.op x y) := by
    first
    | (have i₁ := eq980
       have i₂ := eq896
       grind)
    | exact superpose eq896 eq980
    | exact resolve eq980 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq980
  have eq995 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq993 eq20
    | exact resolve eq20 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq993
  have eq1030 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq995
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq995
    | exact resolve eq995 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq995
  have eq1093 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1030 eq26
    | exact resolve eq26 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1114 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1030 eq924
    | exact resolve eq924 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq1214 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq1030 eq927
    | exact resolve eq927 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927 eq1030
  have eq1222 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1214 eq56
    | exact resolve eq56 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1214
  have eq1234 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1114 eq1222
    | exact resolve eq1222 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1287 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1093 eq586
    | exact resolve eq586 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1315 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1234 eq1287
    | exact resolve eq1287 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234 eq1287
  have eq1328 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1315 eq586
    | exact resolve eq586 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq1330 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1315 eq1328
    | exact resolve eq1328 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315 eq1328
  have eq1334 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1114 eq1330
    | exact resolve eq1330 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114 eq1330
  have eq1336 : False := by grind
  exact eq1336

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq136 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq148 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq150 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
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
  have eq617 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq136 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136
    | exact resolve eq136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq641 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq617 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq617
    | (have j0 := eq617 X0
       grind)
    | exact resolve eq617 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq617
  have eq644 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq641 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq641
    | (have j0 := eq641 X0
       grind)
    | exact resolve eq641 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq645 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq644 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq644 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq644 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq656 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq645 (σ X0)
       grind)
    | exact superpose eq645 eq15
    | exact resolve eq15 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq656 X0
       have i₂ := eq645 X0
       grind)
    | exact superpose eq645 eq656
    | exact resolve eq656 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq656
  have eq2406 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq148 x y
       grind)
    | exact superpose eq148 eq16
    | (have j1 := eq148 x y
       grind)
    | exact resolve eq16 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq5803 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq150 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq150
    | exact resolve eq150 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq5890 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5803 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5803
    | (have j0 := eq5803 X0 X1
       grind)
    | exact resolve eq5803 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5803
  have eq16855 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2406
       have i₂ := eq5890 x y
       grind)
    | exact superpose eq5890 eq2406
    | (have j1 := eq5890 (σ x) (σ y)
       grind)
    | (have r₁ := eq2406
       have r₂ := eq5890 x y
       grind)
    | (have r₁ := eq2406
       have r₂ := eq5890 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2406
       have r₂ := eq5890 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2406 eq5890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16856 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq16855
  have eq16858 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16856
       grind)
    | exact superpose eq16856 eq16
    | exact resolve eq16 eq16856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16856
  have eq16859 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq16858
       have r₂ := eq675 x
       grind)
    | exact resolve eq16858 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16858
  have eq16862 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq16859
       grind)
    | exact superpose eq16859 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq16859
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16859
       grind)
    | exact resolve eq12 eq16859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16859
  have eq16911 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq16862
  have eq17153 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2406
       have i₂ := eq16911
       grind)
    | exact superpose eq16911 eq2406
    | exact resolve eq2406 eq16911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2406 eq16911
  have eq17154 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq17153
  have eq17155 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq17154
  have eq17171 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq17155
       grind)
    | exact superpose eq17155 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq17155
       grind)
    | exact resolve eq12 eq17155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17155
  have eq17220 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17171
  have eq17250 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17220
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17220
    | exact resolve eq17220 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17220
  have eq18349 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17250
       grind)
    | exact superpose eq17250 eq16
    | exact resolve eq16 eq17250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17250
  have eq18414 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18349
       have i₂ := eq5890 x y
       grind)
    | exact superpose eq5890 eq18349
    | (have j1 := eq5890 x y
       grind)
    | (have r₁ := eq18349
       have r₂ := eq5890 x y
       grind)
    | (have r₁ := eq18349
       have r₂ := eq5890 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq18349
       have r₂ := eq5890 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq18349 eq5890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5890
  have eq18415 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq18414
  have eq18419 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18415
       grind)
    | exact superpose eq18415 eq16
    | exact resolve eq16 eq18415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18415
  have eq18426 : y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18419
       have r₂ := eq675 x
       grind)
    | exact resolve eq18419 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18419
  have eq18429 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18426
       grind)
    | exact superpose eq18426 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq18426
       grind)
    | exact resolve eq12 eq18426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18426
  have eq18478 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq18429
  have eq18618 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18349
       have i₂ := eq18478
       grind)
    | exact superpose eq18478 eq18349
    | exact resolve eq18349 eq18478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18349 eq18478
  have eq18622 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq18618
  have eq18623 : (σ x) = (σ y) := by grind
  clear eq18622
  have eq18624 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18623
       grind)
    | exact superpose eq18623 eq16
    | exact resolve eq16 eq18623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18625 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18623
       grind)
    | exact superpose eq18623 eq10
    | exact resolve eq10 eq18623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18623
  have eq18709 : x = y := by
    first
    | (have i₁ := eq18625
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18625
    | exact resolve eq18625 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18625
  have eq18710 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18624
       have i₂ := eq675 x
       grind)
    | exact superpose eq675 eq18624
    | exact resolve eq18624 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq18624
  have eq18713 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18710
       have i₂ := eq18709
       grind)
    | exact superpose eq18709 eq18710
    | exact resolve eq18710 eq18709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18709 eq18710
  have eq18714 : False := by grind
  exact eq18714

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq23
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X2) (M.op X0 (M.op X2 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (M.op X0 X1) (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X1) (M.op X0 (M.op X1 x))
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq473 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq476 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq720 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq468 x y
       grind)
    | exact superpose eq468 eq16
    | (have j1 := eq468 x y
       grind)
    | exact resolve eq16 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq741 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq468 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq468 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq742 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq744 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq740 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq746 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq744 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq744
    | (have j0 := eq744 X0
       grind)
    | exact resolve eq744 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq4207 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq476 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq476
    | exact resolve eq476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq4254 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4207 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4207
    | (have j0 := eq4207 X0 X1
       grind)
    | exact resolve eq4207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4207
  have eq4407 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    grind
  clear eq746
  have eq4409 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4407 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4407
    | (have j0 := eq4407 X0
       grind)
    | exact resolve eq4407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4407
  have eq4544 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq473 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq473
    | exact resolve eq473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq4631 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4544 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq4544
    | (have j0 := eq4544 X0 X1
       grind)
    | exact resolve eq4544 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4544
  have eq4663 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (σ (k (τ (M.op X0 X1)) X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (k X0 X1) X2
       have i₂ := eq4631 X0 X1
       grind)
    | exact superpose eq4631 eq18
    | (have j1 := eq4631 X0 X1
       grind)
    | exact resolve eq18 eq4631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4631
  have eq4771 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (k (M.op X0 X1) (σ X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4663 X0 X1 X2
       have i₂ := eq18 (M.op X0 X1) X2
       grind)
    | exact superpose eq18 eq4663
    | (have j0 := eq4663 X0 X1 X2
       grind)
    | exact resolve eq4663 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4663
  have eq15812 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    grind
  clear eq4409
  have eq15891 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq15812 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq15812
    | (have j0 := eq15812 X0
       grind)
    | exact resolve eq15812 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15812
  have eq15892 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq15891 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15891
  have eq15923 : ∀ X0 : G, (σ (k (σ (k X0 X0)) (σ X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15892 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq15892
    | exact resolve eq15892 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15942 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 (σ (τ X0))) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15892 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq15892
    | exact resolve eq15892 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16045 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq15942 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15942
    | exact resolve eq15942 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15942
  have eq16057 : ∀ X0 : G, (σ (σ (k (k X0 X0) X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15923 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq15923
    | exact resolve eq15923 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15923
  have eq16075 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (σ (k (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq16045 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq16045
    | exact resolve eq16045 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16045
  have eq16097 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (k (σ (τ X0)) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq16075 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq16075
    | exact resolve eq16075 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16075
  have eq16114 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq16097 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16097
    | exact resolve eq16097 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16097
  have eq16165 : ∀ X0 : G, (k (τ (k X0 X0)) (τ X0)) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16114 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq16114
    | exact resolve eq16114 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16188 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4771 (σ X0) (σ X0) X0
       have i₂ := eq16114 (σ X0)
       grind)
    | exact superpose eq16114 eq4771
    | (have j0 := eq4771 (σ X0) (σ X0) x
       grind)
    | exact resolve eq4771 eq16114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4771
  have eq16239 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq16188 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16188
  have eq16287 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16239 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq16239
    | (have j0 := eq16239 X0
       grind)
    | exact resolve eq16239 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16239
  have eq16307 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16165 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq16165
    | exact resolve eq16165 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16165
  have eq16354 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16287 X0
       have i₂ := eq15892 X0
       grind)
    | exact superpose eq15892 eq16287
    | (have j0 := eq16287 X0
       grind)
    | exact resolve eq16287 eq15892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15892 eq16287
  have eq16368 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16307 X0
       have i₂ := eq16114 X0
       grind)
    | exact superpose eq16114 eq16307
    | exact resolve eq16307 eq16114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16307
  have eq16409 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16354 X0
       have i₂ := eq16114 X0
       grind)
    | exact superpose eq16114 eq16354
    | (have j0 := eq16354 X0
       grind)
    | exact resolve eq16354 eq16114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16354
  have eq16445 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq16409
  have eq17592 : ∀ X0 : G, (σ (σ (k (σ (k X0 X0)) (σ X0)))) = (M.op (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq16057 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq16057
    | exact resolve eq16057 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16057
  have eq17804 : ∀ X0 : G, (σ (σ (σ (k (k X0 X0) X0)))) = (M.op (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17592 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq17592
    | exact resolve eq17592 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17592
  have eq17843 : ∀ X0 : G, (σ (σ (σ (M.op (k X0 X0) X0)))) = (M.op (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17804 X0
       have i₂ := eq16114 X0
       grind)
    | exact superpose eq16114 eq17804
    | exact resolve eq17804 eq16114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16114 eq17804
  have eq21735 : ∀ X0 : G, (σ (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0))))) = (M.op (σ (σ (k X0 (σ (τ X0))))) (σ (σ (σ (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq17843 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq17843
    | exact resolve eq17843 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17843
  have eq21849 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq21735 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21735
    | exact resolve eq21735 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21735
  have eq21885 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (σ (M.op (τ (k X0 X0)) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq21849 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq21849
    | exact resolve eq21849 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21849
  have eq21911 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (σ (τ (M.op (k X0 X0) X0))))) := by
    intro X0
    first
    | (have i₁ := eq21885 X0
       have i₂ := eq16368 X0
       grind)
    | exact superpose eq16368 eq21885
    | exact resolve eq21885 eq16368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21885
  have eq21932 : ∀ X0 : G, (σ (σ (M.op (k X0 X0) X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq21911 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq21911
    | exact resolve eq21911 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21911
  have eq21996 : ∀ X0 : G, (M.op (σ (σ (k (τ X0) (τ X0)))) (σ X0)) = (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq21932 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21932
    | exact resolve eq21932 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21932
  have eq22108 : ∀ X0 : G, (σ (σ (M.op (τ (k X0 X0)) (τ X0)))) = (M.op (σ (σ (τ (k X0 X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21996 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq21996
    | exact resolve eq21996 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21996
  have eq22143 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (σ (M.op (τ (k X0 X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq22108 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq22108
    | exact resolve eq22108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22108
  have eq22169 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (σ (τ (M.op (k X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq22143 X0
       have i₂ := eq16368 X0
       grind)
    | exact superpose eq16368 eq22143
    | exact resolve eq22143 eq16368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22143
  have eq22189 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq22169 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq22169
    | exact resolve eq22169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22169
  have eq28463 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq720
       have i₂ := eq4254 x y
       grind)
    | exact superpose eq4254 eq720
    | (have j1 := eq4254 (σ x) (σ y)
       grind)
    | (have r₁ := eq720
       have r₂ := eq4254 x y
       grind)
    | exact resolve eq720 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq28464 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq28463
  have eq34319 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op (k X0 X0) X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq16445 X0
       grind)
    | exact superpose eq16445 eq64
    | (have j1 := eq16445 X0
       grind)
    | exact resolve eq64 eq16445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq34320 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq69 (σ X0) (σ X0)
       have i₂ := eq16445 X0
       grind)
    | exact superpose eq16445 eq69
    | (have j1 := eq16445 X0
       grind)
    | exact resolve eq69 eq16445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq16445
  have eq35620 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (k (τ X0) (τ X0)) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34319 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34319
    | exact resolve eq34319 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34319
  have eq35767 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ (k X0 X0)) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35620 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq35620
    | (have j0 := eq35620 X0
       grind)
    | exact resolve eq35620 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35620
  have eq35794 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (τ (M.op (k X0 X0) X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35767 X0
       have i₂ := eq16368 X0
       grind)
    | exact superpose eq16368 eq35767
    | (have j0 := eq35767 X0
       grind)
    | exact resolve eq35767 eq16368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35767
  have eq35814 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (k X0 X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35794 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq35794
    | (have j0 := eq35794 X0
       grind)
    | exact resolve eq35794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35794
  have eq39464 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (k (τ X0) (τ X0)) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34320 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34320
    | exact resolve eq34320 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34320
  have eq39609 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (τ (k X0 X0)) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39464 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq39464
    | (have j0 := eq39464 X0
       grind)
    | exact resolve eq39464 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq39464
  have eq39622 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (τ (M.op (k X0 X0) X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39609 X0
       have i₂ := eq16368 X0
       grind)
    | exact superpose eq16368 eq39609
    | (have j0 := eq39609 X0
       grind)
    | exact resolve eq39609 eq16368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16368 eq39609
  have eq39631 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39622 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq39622
    | (have j0 := eq39622 X0
       grind)
    | exact resolve eq39622 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39622
  have eq39665 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 (k X0 X0) X0 X0
       have i₂ := eq39631 X0
       grind)
    | exact superpose eq39631 eq63
    | (have j1 := eq39631 X0
       grind)
    | exact resolve eq63 eq39631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq39631
  have eq39915 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39665 (σ x)
       have i₂ := eq468 x x
       grind)
    | exact superpose eq468 eq39665
    | (have j0 := eq39665 (σ X0)
       have j1 := eq468 X0 X0
       grind)
    | exact resolve eq39665 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq39665
  have eq40014 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq39915 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39915
  have eq40025 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq40014 X0
       have j1 := eq743 X0
       grind)
    | (have r₁ := eq40014 X0
       have r₂ := eq743 X0
       grind)
    | exact resolve eq40014 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq40014
  have eq40029 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40025 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq40025
    | (have j0 := eq40025 X0
       grind)
    | exact resolve eq40025 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40025
  have eq45304 : ∀ X0 : G, (σ (τ X0)) = (M.op (k X0 (σ (τ X0))) (M.op (σ (τ X0)) (k X0 (σ (τ X0))))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40029 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq40029
    | (have j0 := eq40029 (τ X0)
       grind)
    | exact resolve eq40029 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq40029
  have eq45424 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq45304 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45304
    | (have j0 := eq45304 X0
       grind)
    | exact resolve eq45304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45304
  have eq45480 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45424 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45424
    | (have j0 := eq45424 X0
       grind)
    | exact resolve eq45424 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45424
  have eq45580 : ∀ X0 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 (k X0 X0) (M.op X0 (k X0 X0))
       have i₂ := eq45480 X0
       grind)
    | exact superpose eq45480 eq76
    | (have j1 := eq45480 X0
       grind)
    | exact resolve eq76 eq45480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq45480
  have eq46749 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35814 X0
       have i₂ := eq45580 X0
       grind)
    | exact superpose eq45580 eq35814
    | (have j0 := eq35814 X0
       have j1 := eq45580 X0
       grind)
    | exact resolve eq35814 eq45580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35814 eq45580
  have eq46895 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq46749 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46749
  have eq47332 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq46895 (σ X0)
       grind)
    | exact superpose eq46895 eq15
    | (have j1 := eq46895 (σ X0)
       grind)
    | exact resolve eq15 eq46895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46895
  have eq49550 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq47332
  have eq49620 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49550 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq49550
    | (have j0 := eq49550 X0
       grind)
    | exact resolve eq49550 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49550
  have eq49621 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq49620 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49620
  have eq49698 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq49621 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49621
    | exact resolve eq49621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50014 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq49698 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq49698
    | exact resolve eq49698 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq49698
  have eq50093 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq50014 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50014
    | exact resolve eq50014 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50014
  have eq50342 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22189 X0
       have i₂ := eq50093 X0
       grind)
    | exact superpose eq50093 eq22189
    | exact resolve eq22189 eq50093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22189
  have eq607746 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq28464
       grind)
    | exact superpose eq28464 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq28464
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq28464
       grind)
    | exact resolve eq13 eq28464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28464
  have eq607837 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq607746
  have eq607838 : x = (M.op y y) ∨ y = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq607837
  have eq607926 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq607838
       have i₂ := eq49621 y
       grind)
    | exact superpose eq49621 eq607838
    | exact resolve eq607838 eq49621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607838
  have eq608015 : y = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq607926
       have i₂ := eq50093 y
       grind)
    | exact superpose eq50093 eq607926
    | exact resolve eq607926 eq50093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607926
  have eq608049 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq741 x y
       have i₂ := eq608015
       grind)
    | exact superpose eq608015 eq741
    | (have j0 := eq741 x y
       grind)
    | exact resolve eq741 eq608015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq608015
  have eq608139 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq608049
  have eq608140 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq608139
  have eq608153 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq608140
       have i₂ := eq49621 y
       grind)
    | exact superpose eq49621 eq608140
    | exact resolve eq608140 eq49621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608140
  have eq608164 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq608153
       have i₂ := eq50093 y
       grind)
    | exact superpose eq50093 eq608153
    | exact resolve eq608153 eq50093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608153
  have eq608165 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq608164
  have eq609354 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq608165
       grind)
    | exact superpose eq608165 eq16
    | exact resolve eq16 eq608165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609421 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq608165
       grind)
    | exact superpose eq608165 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq608165
       grind)
    | exact resolve eq13 eq608165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608165
  have eq609512 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq609421
  have eq609545 : (σ x) = (σ (k y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq609512
       have i₂ := eq49621 y
       grind)
    | exact superpose eq49621 eq609512
    | exact resolve eq609512 eq49621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49621 eq609512
  have eq609606 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq609545
       have i₂ := eq50093 y
       grind)
    | exact superpose eq50093 eq609545
    | exact resolve eq609545 eq50093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50093 eq609545
  have eq609607 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq609606
  have eq609624 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq609607
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq609607
    | exact resolve eq609607 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609607
  have eq609647 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4254 x y
       have i₂ := eq609624
       grind)
    | exact superpose eq609624 eq4254
    | (have j0 := eq4254 x y
       grind)
    | exact resolve eq4254 eq609624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4254 eq609624
  have eq609957 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq609647
  have eq610148 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq609957
       have r₂ := eq609354
       grind)
    | exact resolve eq609957 eq609354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609957
  have eq610436 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq609354
       have i₂ := eq610148
       grind)
    | exact superpose eq610148 eq609354
    | exact resolve eq609354 eq610148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609354 eq610148
  have eq610532 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq610436
  have eq610533 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq610532
  have eq610685 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq610533
       grind)
    | exact superpose eq610533 eq10
    | exact resolve eq10 eq610533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610533
  have eq611168 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq610685
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq610685
    | exact resolve eq610685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610685
  have eq611169 : x = (M.op y y) := by grind
  clear eq611168
  have eq611435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50342 y
       have i₂ := eq611169
       grind)
    | exact superpose eq611169 eq50342
    | exact resolve eq50342 eq611169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50342 eq611169
  have eq611734 : False := by grind
  exact eq611734

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  clear eq55 eq57
  have eq81 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
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
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq93 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq66 X1
       grind)
    | exact superpose eq66 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq87
  have eq267 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq276 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq280 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq276 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq276 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq290 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq280 X0 X1
       have j1 := eq81 X1 (σ X0)
       grind)
    | (have r₁ := eq280 X0 X0
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq280 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq280
  have eq298 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq290
    | (have j0 := eq290 X0 X1
       grind)
    | exact resolve eq290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq299 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq305 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq299 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq299
    | exact resolve eq299 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq299 x y
       grind)
    | exact superpose eq299 eq16
    | exact resolve eq16 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq385 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq305 X0 (τ X1)
       grind)
    | exact superpose eq305 eq18
    | exact resolve eq18 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq305
  have eq398 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq385 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq385
    | exact resolve eq385 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq404 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq398 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq398
    | exact resolve eq398 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq416 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq316
       have i₂ := eq404 x y
       grind)
    | exact superpose eq404 eq316
    | exact resolve eq316 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq404
  have eq417 : False := by grind
  exact eq417

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pyx_Equation1446 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1446 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
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
  have eq175 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X0 X2) (M.op X0 (M.op X2 x))
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X1) X0 (M.op X1 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : x = (M.op (M.op x y) (M.op x (k y y))) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq175
    | exact resolve eq175 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq191 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (k (σ y) (σ y)))) := by
    first
    | (have i₁ := eq176 sF3
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq213 : x = (M.op (M.op x (M.op x y)) (k x x)) := by
    first
    | (have i₁ := eq187 x
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq187
    | exact resolve eq187 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq222 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq193 sF2
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq193
    | exact resolve eq193 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq541 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = y := by
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
  have eq552 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
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
  have eq570 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq552
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq552
    | exact resolve eq552 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq581 : (M.op x y) = (k y x) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq541
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq541
    | exact resolve eq541 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq776 : (M.op x y) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq185 eq180
    | exact resolve eq180 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq778 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq191 eq180
    | exact resolve eq180 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq815 : x = (M.op (M.op x y) (M.op x (M.op x y))) := by
    first
    | exact superpose eq776 eq180
    | exact resolve eq180 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq827 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq778 eq180
    | exact resolve eq180 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1588 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq581
       grind)
    | exact superpose eq581 eq39
    | exact resolve eq39 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq1589 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1588
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1588
    | exact resolve eq1588 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588
  have eq1591 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq1589
    | exact resolve eq1589 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589
  have eq3409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq1591 eq570
    | exact resolve eq570 eq1591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq1591
  have eq3418 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq3409
       have r₂ := eq27
       grind)
    | exact resolve eq3409 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409
  have eq3430 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq3418 eq141
    | exact resolve eq141 eq3418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq3418
  have eq3445 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq29 eq3430
    | exact resolve eq3430 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3430
  have eq3446 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3445
  have eq3460 : x = (M.op (M.op x (M.op x y)) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq213
       have i₂ := eq3446
       grind)
    | exact superpose eq3446 eq213
    | exact resolve eq213 eq3446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq3466 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3446
       grind)
    | exact superpose eq3446 eq39
    | exact resolve eq39 eq3446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3481 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3466
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3466
    | exact resolve eq3466 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3466
  have eq3503 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3481 eq222
    | exact resolve eq222 eq3481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq3614 : (M.op x x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3460 eq181
    | exact resolve eq181 eq3460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3460
  have eq3643 : (k x x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3614
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq3614
    | exact resolve eq3614 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3614
  have eq3653 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3446 eq3643
    | exact resolve eq3643 eq3446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3446 eq3643
  have eq3664 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3653 eq815
    | exact resolve eq815 eq3653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815 eq3653
  have eq3743 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3664 eq776
    | exact resolve eq776 eq3664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq3664
  have eq3775 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3743
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq3743
    | exact resolve eq3743 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3743
  have eq3787 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3775
       grind)
    | exact superpose eq3775 eq39
    | exact resolve eq39 eq3775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775
  have eq3798 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3787
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3787
    | exact resolve eq3787 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3787
  have eq3800 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq3798
    | exact resolve eq3798 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3798
  have eq3802 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq3481 eq3800
    | exact resolve eq3800 eq3481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3800
  have eq5029 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3503 eq181
    | exact resolve eq181 eq3503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq3503
  have eq5062 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5029
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq5029
    | exact resolve eq5029 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5029
  have eq5072 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3481 eq5062
    | exact resolve eq5062 eq3481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5062
  have eq5083 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5072 eq827
    | exact resolve eq827 eq5072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq5072
  have eq5165 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5083 eq778
    | exact resolve eq778 eq5083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778 eq5083
  have eq5201 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5165
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq5165
    | exact resolve eq5165 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5165
  have eq5204 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3481 eq5201
    | exact resolve eq5201 eq3481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3481 eq5201
  have eq5206 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5204 eq27
    | exact resolve eq27 eq5204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5204
  have eq5262 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq5206
       have r₂ := eq3802
       grind)
    | exact resolve eq5206 eq3802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3802 eq5206
  have eq5278 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq5262 eq31
    | exact resolve eq31 eq5262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5262
  have eq5306 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq5278
    | exact resolve eq5278 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5278
  have eq5307 : x = y := by grind
  clear eq5306
  have eq5319 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5307
       grind)
    | exact superpose eq5307 eq18
    | exact resolve eq18 eq5307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq5320 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5307
       grind)
    | exact superpose eq5307 eq24
    | exact resolve eq24 eq5307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5307
  have eq5331 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq5320
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5320
    | exact resolve eq5320 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5320
  have eq5332 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq5319
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq5319
    | exact resolve eq5319 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5319
  have eq5333 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5331 eq26
    | exact resolve eq26 eq5331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5331
  have eq5361 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq5333
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq5333
    | exact resolve eq5333 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq5333
  have eq5372 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq5332
       grind)
    | exact superpose eq5332 eq39
    | exact resolve eq39 eq5332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq5332
  have eq5381 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq5372
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5372
    | exact resolve eq5372 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5372
  have eq5383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5361 eq5381
    | exact resolve eq5381 eq5361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5361 eq5381
  have eq5385 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5383
    | exact resolve eq5383 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5383
  have eq5387 : False := by grind
  exact eq5387

/-- `Equation1465`: `x = (x ◇ y) ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_x_pxy_Equation1465 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1465 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1465.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq18
  have eq32 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X1) X0 (M.op X1 X2)
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq23
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X3) (M.op X0 (M.op X2 X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32 X0 (M.op X2 (M.op X1 X0)) (M.op X0 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op X1 (M.op X3 (M.op X4 (M.op X1 X2)))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq57 X3 (M.op X1 X2) X4 (M.op x (M.op X2 X1))
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq57
    | exact resolve eq57 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X2 X3)) = (M.op X0 (M.op X4 X3)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq62 X0 (M.op X2 X3) X4 (M.op X3 x)
       have i₂ := eq57 X0 X3 X2 x
       grind)
    | exact superpose eq57 eq62
    | exact resolve eq62 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq129 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq129 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq129
    | (have j0 := eq129 (σ X0) (σ X1)
       grind)
    | exact resolve eq129 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X0
       have i₂ := eq129 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq129 X0 (M.op X1 X1)
       grind)
    | exact superpose eq129 eq12
    | (have j0 := eq12 X2 X0
       have j1 := eq129 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq129 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq129 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq147 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq426 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq412 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq427 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq426 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq433 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq427 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq427
    | exact resolve eq427 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq427 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq427
    | exact resolve eq427 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq435 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq434 X0
       have i₂ := eq427 X0
       grind)
    | exact superpose eq427 eq434
    | exact resolve eq434 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq436 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq433 X0
       have i₂ := eq427 X0
       grind)
    | exact superpose eq427 eq433
    | exact resolve eq433 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq433
  have eq442 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op (τ X0) X2) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 (τ X0) (τ X0) X2
       have i₂ := eq435 X0
       grind)
    | exact superpose eq435 eq57
    | exact resolve eq57 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134 x y
       grind)
    | exact superpose eq134 eq16
    | (have j1 := eq134 x y
       grind)
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq536 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (σ X0) (σ X0)
       have i₂ := eq436 X0
       grind)
    | exact superpose eq436 eq32
    | exact resolve eq32 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq752 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq442 X0 X1 (τ X0)
       have i₂ := eq435 X0
       grind)
    | exact superpose eq435 eq442
    | exact resolve eq442 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq442
  have eq1245 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X1 X0))) = (M.op (τ X0) (M.op X2 (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq752 (M.op X0 (M.op X2 X0)) X1
       have i₂ := eq57 X0 X0 X2 (M.op X2 X0)
       grind)
    | exact superpose eq57 eq752
    | exact resolve eq752 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq752
  have eq2193 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (τ (M.op (σ X0) (M.op X2 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1245 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1245
    | exact resolve eq1245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245
  have eq3576 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq472
       have i₂ := eq436 x
       grind)
    | exact superpose eq436 eq472
    | exact resolve eq472 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq472
  have eq3903 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3576
       have i₂ := eq129 x y
       grind)
    | exact superpose eq129 eq3576
    | (have j1 := eq129 x y
       grind)
    | exact resolve eq3576 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq3576
  have eq3908 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq3903
  have eq3921 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq3908
       grind)
    | exact superpose eq3908 eq10
    | exact resolve eq10 eq3908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3908
  have eq3957 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3921
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3921
    | exact resolve eq3921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3921
  have eq3958 : y = (M.op x x) := by grind
  clear eq3957
  have eq3969 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq536 x x
       have i₂ := eq3958
       grind)
    | exact superpose eq3958 eq536
    | exact resolve eq536 eq3958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq3990 : ∀ X0 X1 : G, (M.op X1 (M.op X0 x)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X1 x x X0
       have i₂ := eq3958
       grind)
    | exact superpose eq3958 eq76
    | exact resolve eq76 eq3958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq3958
  have eq4880 : ∀ X1 : G, (τ (M.op (σ x) (σ y))) = (M.op x (M.op X1 x)) := by
    intro X1
    first
    | (have i₁ := eq2193 x X1 (M.op (σ y) x)
       have i₂ := eq3969 x
       grind)
    | exact superpose eq3969 eq2193
    | exact resolve eq2193 eq3969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193 eq3969
  have eq4907 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4880 x
       have i₂ := eq3990 x x
       grind)
    | exact superpose eq3990 eq4880
    | exact resolve eq4880 eq3990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3990 eq4880
  have eq5923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq4907
       grind)
    | exact superpose eq4907 eq11
    | exact resolve eq11 eq4907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4907
  have eq5946 : False := by grind
  exact eq5946

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pyx_y_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq62 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
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
  have eq67 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq62 X0 X1 X2
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq120 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0 X1
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq9
    | exact resolve eq9 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X0
       have i₂ := eq120 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq120 eq9
    | exact resolve eq9 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq134 X0
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq134
    | exact resolve eq134 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq142 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq125 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq125
    | exact resolve eq125 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq744 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X2 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq68
    | exact resolve eq68 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq967 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq744 X0 x X1
       grind)
    | exact superpose eq744 eq9
    | exact resolve eq9 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq1021 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq967 X0 X0 x
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq967
    | exact resolve eq967 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq1066 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1021 (σ X1) X1
       have i₂ := eq15 X1 X1
       grind)
    | exact superpose eq15 eq1021
    | exact resolve eq1021 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq2279 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1066 (M.op X0 (k X0 X0)) X1
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq1066
    | exact resolve eq1066 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq2462 : ∀ X0 X1 : G, (σ (M.op X0 (k X0 X0))) = (M.op (σ (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0)))) (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq142 (M.op X0 (k X0 X0)) (M.op (σ X0) X1)
       have i₂ := eq2279 X0 X1
       grind)
    | exact superpose eq2279 eq142
    | exact resolve eq142 eq2279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq2279
  have eq2503 : ∀ X0 X1 : G, (σ (M.op X0 (k X0 X0))) = (M.op (σ X0) (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2462 X0 X1
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq2462
    | exact resolve eq2462 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq2462
  have eq2517 : ∀ X0 : G, (σ (M.op X0 (k X0 X0))) = (M.op (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2503 X0 x
       have i₂ := eq67 (σ X0) (σ X0) x
       grind)
    | exact superpose eq67 eq2503
    | exact resolve eq2503 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2503
  have eq2522 : ∀ X0 : G, (M.op (σ X0) (k (σ X0) (σ X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2517 X0
       have i₂ := eq120 (σ X0)
       grind)
    | exact superpose eq120 eq2517
    | exact resolve eq2517 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2517
  have eq2526 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2522 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2522
    | exact resolve eq2522 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522
  have eq8476 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 (M.op X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8477 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8476 X0 X1
       have i₂ := eq120 X1
       grind)
    | exact superpose eq120 eq8476
    | (have j0 := eq8476 X0 X1
       grind)
    | exact resolve eq8476 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq8476
  have eq8705 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8477 (σ y) (σ x)
       grind)
    | exact superpose eq8477 eq16
    | (have j1 := eq8477 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq8477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8747 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq8705
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8705
    | exact resolve eq8705 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8705
  have eq8757 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq8747
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq8747
    | exact resolve eq8747 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8747
  have eq14175 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq8757
       have i₂ := eq8477 y x
       grind)
    | exact superpose eq8477 eq8757
    | (have j1 := eq8477 y x
       grind)
    | exact resolve eq8757 eq8477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8477 eq8757
  have eq14176 : (σ y) = (σ (k x x)) ∨ y = (k x x) := by grind
  clear eq14175
  have eq14182 : (k x x) = (τ (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq14176
       grind)
    | exact superpose eq14176 eq10
    | exact resolve eq10 eq14176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14176
  have eq14223 : y = (k x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14182
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq14182
    | exact resolve eq14182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14182
  have eq14224 : y = (k x x) := by grind
  clear eq14223
  have eq14274 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2526 x
       have i₂ := eq14224
       grind)
    | exact superpose eq14224 eq2526
    | exact resolve eq2526 eq14224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526 eq14224
  have eq14299 : False := by grind
  exact eq14299
