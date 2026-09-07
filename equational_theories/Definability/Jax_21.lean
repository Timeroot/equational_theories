import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation436`: `x = x ◇ (y ◇ (y ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation436 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law436 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law436.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq35
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq95 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq92 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq92 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq92 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq92 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq183 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq95 (σ X0) (σ X1)
       grind)
    | exact superpose eq95 eq15
    | (have j1 := eq95 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq95 (τ X0) X1
       grind)
    | exact superpose eq95 eq18
    | (have j1 := eq95 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq95
  have eq646 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq185 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq185
    | exact resolve eq185 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq685 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq646 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq646
    | (have j0 := eq646 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq646 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq1992 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq183 x y
       grind)
    | exact superpose eq183 eq16
    | (have j1 := eq183 x y
       grind)
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq2203 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1992
       have i₂ := eq685 x y
       grind)
    | exact superpose eq685 eq1992
    | (have j1 := eq685 (σ x) (σ y)
       grind)
    | (have r₁ := eq1992
       have r₂ := eq685 x y
       grind)
    | (have r₁ := eq1992
       have r₂ := eq685 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1992
       have r₂ := eq685 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1992 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq1992
  have eq2204 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2203
  have eq2223 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2204
       grind)
    | exact superpose eq2204 eq10
    | exact resolve eq10 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204
  have eq2270 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2223
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2223
    | exact resolve eq2223 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223
  have eq2271 : x = y := by grind
  clear eq2270
  have eq2337 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2271
       grind)
    | exact superpose eq2271 eq16
    | exact resolve eq16 eq2271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271
  have eq2338 : False := by grind
  exact eq2338

/-- `Equation436`: `x = x ◇ (y ◇ (y ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_Equation436 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law436 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law436.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq55 (σ X0) (σ X1)
       grind)
    | exact superpose eq55 eq15
    | (have j1 := eq55 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq55 (τ X0) X1
       grind)
    | exact superpose eq55 eq18
    | (have j1 := eq55 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq55
  have eq186 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61
    | exact resolve eq61 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq186
    | (have j0 := eq186 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq186 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq595 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq60 x y
       grind)
    | exact superpose eq60 eq16
    | (have j1 := eq60 x y
       grind)
    | exact resolve eq16 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq616 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq595
       have i₂ := eq210 x y
       grind)
    | exact superpose eq210 eq595
    | (have j1 := eq210 (σ x) (σ y)
       grind)
    | (have r₁ := eq595
       have r₂ := eq210 x y
       grind)
    | (have r₁ := eq595
       have r₂ := eq210 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq595
       have r₂ := eq210 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq595 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq595
  have eq617 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq616
  have eq703 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq617
       grind)
    | exact superpose eq617 eq10
    | exact resolve eq10 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq739 : x = y ∨ x = y := by
    first
    | (have i₁ := eq703
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq703
    | exact resolve eq703 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq740 : x = y := by grind
  clear eq739
  have eq835 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq740
       grind)
    | exact superpose eq740 eq16
    | exact resolve eq16 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq836 : False := by grind
  exact eq836

/-- `Equation436`: `x = x ◇ (y ◇ (y ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation436 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law436 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law436.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq46 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ X1 = X2 ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X2
       have i₂ := eq14 X1 X2
       grind)
    | (have i₁ := eq14 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X1 X2
       have j1 := eq14 X1 X2
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq46 X1 X1 X2
       have j1 := eq55 X1 X1 X2
       grind)
    | (have r₁ := eq46 X0 X1 X2
       have r₂ := eq55 X0 X1 X2
       grind)
    | (have r₁ := eq46 X1 X0 X2
       have r₂ := eq55 X0 X1 X2
       grind)
    | (have r₁ := eq46 X0 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq55 X0 X1 X2
       grind)
    | exact resolve eq46 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq55
  have eq128 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq129 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq128 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq130 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq129 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq193 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq130 (σ X0) (σ X1)
       grind)
    | exact superpose eq130 eq15
    | (have j1 := eq130 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq130 (τ X0) X1
       grind)
    | exact superpose eq130 eq18
    | (have j1 := eq130 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq130
  have eq447 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq195 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq195
    | exact resolve eq195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq473 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq447
    | (have j0 := eq447 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq447 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq1659 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq193 x y
       grind)
    | exact superpose eq193 eq16
    | (have j1 := eq193 x y
       grind)
    | exact resolve eq16 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq1754 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1659
       have i₂ := eq473 x y
       grind)
    | exact superpose eq473 eq1659
    | (have j1 := eq473 (σ x) (σ y)
       grind)
    | (have r₁ := eq1659
       have r₂ := eq473 x y
       grind)
    | (have r₁ := eq1659
       have r₂ := eq473 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1659
       have r₂ := eq473 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1659 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq1659
  have eq1755 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1754
  have eq1836 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1755
       grind)
    | exact superpose eq1755 eq10
    | exact resolve eq10 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq1878 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1836
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1836
    | exact resolve eq1836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq1879 : x = y := by grind
  clear eq1878
  have eq1954 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1879
       grind)
    | exact superpose eq1879 eq16
    | exact resolve eq16 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq1955 : False := by grind
  exact eq1955

/-- `Equation4386`: `x ◇ (x ◇ x) = (y ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pxy_y_pxy_Equation4386 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4386 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4386.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X1) := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X1 X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq23
  have eq63 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X2 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X2 X1
       have j1 := eq14 X2 X1
       grind)
    | exact resolve eq14 eq14
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
  have eq69 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq70 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X1) X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq71 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op X0 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq73 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq74 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq72 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq72 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq75 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq71 (M.op X0 X1) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq71 (k X0 X1) (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq71 (M.op X0 (k X1 X1)) X1
       have r₂ := eq12 X0 (k X1 X1)
       grind)
    | exact resolve eq71 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq76 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X1) X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq70 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq70 (M.op (M.op X2 X0) X2) X0 X2
       have r₂ := eq12 X0 (M.op (M.op X2 X0) X2)
       grind)
    | (have r₁ := eq70 X0 X1 (M.op X1 X0)
       have r₂ := eq12 (M.op (M.op X1 X0) X1) (M.op X1 X0)
       grind)
    | (have r₁ := eq70 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq70 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq77 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq73 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq73 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq78 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | (have r₁ := eq63 (M.op X0 X1) X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq63 X1 X1 (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq63 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq63 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq79 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq78 X0 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | (have r₁ := eq78 (M.op X0 X1) X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq78 X1 X1 (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq78 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq78 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq113 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) = (M.op X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X2 X1)
       have i₂ := eq24 X2 X1 X0
       grind)
    | (have i₁ := eq9 X2 (M.op X2 X1)
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
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
  have eq123 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq77 (τ X0) X1
       grind)
    | exact superpose eq77 eq18
    | (have j1 := eq77 (τ X0) X1
       grind)
    | exact resolve eq18 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq125 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq74 (σ X0) (σ X1)
       grind)
    | exact superpose eq74 eq15
    | (have j1 := eq74 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq155 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq25 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq155 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq155 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq155 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq244 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq76 X1 X0 x
       grind)
    | exact superpose eq76 eq9
    | (have j1 := eq76 X1 X0 x
       grind)
    | exact resolve eq9 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq483 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X0
       have i₂ := eq14 X0 (σ X0)
       grind)
    | (have i₁ := eq66 X0 X1
       have i₂ := eq14 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq14 eq66
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq66 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq66 X1 X0
       grind)
    | exact superpose eq66 eq10
    | (have j1 := eq66 X1 X0
       grind)
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X2
       have i₂ := eq66 X1 X0
       grind)
    | exact superpose eq66 eq15
    | (have j1 := eq66 X1 X0
       grind)
    | exact resolve eq15 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq66 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq551 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq549 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq562 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq483 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq583 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq562 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq562 (M.op X0 (σ (k X1 X1))) X1
       have r₂ := eq12 X0 (σ (k X1 X1))
       grind)
    | (have r₁ := eq562 (M.op X0 (σ X1)) X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq562 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq562 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1075 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq551 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq551
    | (have j0 := eq551 (τ X0)
       grind)
    | exact resolve eq551 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq1078 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1075 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1075
    | (have j0 := eq1075 X0
       grind)
    | exact resolve eq1075 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1081 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1078 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1078
    | (have j0 := eq1078 X0
       grind)
    | exact resolve eq1078 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1267 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq123 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq123
    | exact resolve eq123 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq1302 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1267 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1267
    | (have j0 := eq1267 X0 X1
       grind)
    | exact resolve eq1267 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq1796 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq116 x y
       grind)
    | exact superpose eq116 eq16
    | (have j1 := eq116 x y
       grind)
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1814 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ X1)) X2) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 (σ X1) (σ X0)
       have i₂ := eq116 X0 X1
       grind)
    | exact superpose eq116 eq24
    | (have j1 := eq116 X0 X1
       grind)
    | exact resolve eq24 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq116
  have eq4689 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq583 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq583
    | (have j0 := eq583 X1 (τ X0)
       grind)
    | exact resolve eq583 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq4809 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4689 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq4689
    | (have j0 := eq4689 X0 X1
       grind)
    | exact resolve eq4689 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4689
  have eq4820 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4809 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4809
    | (have j0 := eq4809 X0 X1
       grind)
    | exact resolve eq4809 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4809
  have eq4827 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq4820 X0 X1
       have j1 := eq75 X1 X0
       grind)
    | (have r₁ := eq4820 X0 X1
       have r₂ := eq75 (k X0 X0) X1
       grind)
    | (have r₁ := eq4820 X0 X0
       have r₂ := eq75 X0 (k X0 X0)
       grind)
    | (have r₁ := eq4820 X0 X1
       have r₂ := eq75 (M.op X1 X0) (k X1 X0)
       grind)
    | exact resolve eq4820 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq4820
  have eq4871 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X0
       have i₂ := eq4827 X0 X1
       grind)
    | (have i₁ := eq77 X0 X1
       have i₂ := eq4827 X0 (k X0 X1)
       grind)
    | exact superpose eq4827 eq77
    | (have j0 := eq77 X0 X1
       have j1 := eq4827 X1 X0
       grind)
    | exact resolve eq77 eq4827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq4916 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq4933 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4916 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4916
  have eq4943 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4933 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq4933
    | (have j0 := eq4933 X0
       grind)
    | exact resolve eq4933 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4933
  have eq5776 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq4943 X0
       grind)
    | exact superpose eq4943 eq9
    | (have j1 := eq4943 X0
       grind)
    | exact resolve eq9 eq4943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4943
  have eq6490 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq171 X0 X0
       have i₂ := eq5776 X0 X0
       grind)
    | exact superpose eq5776 eq171
    | (have j0 := eq171 X0 X0
       have j1 := eq5776 X0 x
       grind)
    | exact resolve eq171 eq5776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq5776
  have eq6570 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6490 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6490
  have eq6598 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6570 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq6570 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq6570 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6570
  have eq6914 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4827 X0 X1
       have i₂ := eq6598 X0
       grind)
    | exact superpose eq6598 eq4827
    | (have j0 := eq4827 X0 X1
       grind)
    | exact resolve eq4827 eq6598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6923 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq6598 (σ X0)
       grind)
    | exact superpose eq6598 eq15
    | exact resolve eq15 eq6598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6929 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq6598 (τ X0)
       grind)
    | exact superpose eq6598 eq36
    | exact resolve eq36 eq6598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6936 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6929 X0
       have i₂ := eq6598 X0
       grind)
    | exact superpose eq6598 eq6929
    | exact resolve eq6929 eq6598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6929
  have eq6942 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6923 X0
       have i₂ := eq6598 X0
       grind)
    | exact superpose eq6598 eq6923
    | exact resolve eq6923 eq6598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6923
  have eq7302 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    grind
  clear eq6936
  have eq7397 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq7302 X0
       have j1 := eq125 (τ (M.op X0 X0)) (τ X0)
       grind)
    | (have r₁ := eq7302 X0
       have r₂ := eq125 (τ (M.op X0 X0)) (τ X0)
       grind)
    | exact resolve eq7302 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq7302
  have eq7410 : ∀ X0 : G, (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq7397 X0
       have i₂ := eq36 X0 (M.op X0 X0)
       grind)
    | exact superpose eq36 eq7397
    | exact resolve eq7397 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7397
  have eq7838 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7410 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq7410 X0
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq7410
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq7410 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7870 : ∀ X0 : G, (σ (τ X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11 (k (M.op X0 X0) X0)
       have i₂ := eq7410 X0
       grind)
    | exact superpose eq7410 eq11
    | exact resolve eq11 eq7410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7873 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 (k (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (k (M.op X0 X0) X0) X1
       have i₂ := eq7410 X0
       grind)
    | exact superpose eq7410 eq36
    | exact resolve eq36 eq7410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7874 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k (k (M.op X0 X0) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (k (M.op X0 X0) X0)
       have i₂ := eq7410 X0
       grind)
    | exact superpose eq7410 eq36
    | exact resolve eq36 eq7410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7410
  have eq7882 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (k (k (M.op X0 X0) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7874 X0 X1
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq7874
    | exact resolve eq7874 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7874
  have eq7883 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (k X1 (k (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7873 X0 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq7873
    | exact resolve eq7873 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7873
  have eq7886 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7870 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7870
    | exact resolve eq7870 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7870
  have eq7902 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq7838 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq7838 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq7838 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7838
  have eq9070 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq6942 X0
       grind)
    | exact superpose eq6942 eq9
    | exact resolve eq9 eq6942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9102 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq6942 X0
       grind)
    | exact superpose eq6942 eq9
    | exact resolve eq9 eq6942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10102 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 (k (M.op X1 X1) X1))) ∨ (k X0 (k (M.op X1 X1) X1)) = (M.op X0 (k (M.op X1 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7882 X1 (k (M.op X1 X1) X1)
       have i₂ := eq4827 (k (M.op X1 X1) X1) X0
       grind)
    | (have i₁ := eq7882 X0 X1
       have i₂ := eq4827 X0 (k (k (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq4827 eq7882
    | (have j1 := eq4827 (k (M.op X1 X1) X1) X0
       grind)
    | exact resolve eq7882 eq4827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4827 eq7882
  have eq10183 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X1)) ∨ (k X0 (k (M.op X1 X1) X1)) = (M.op X0 (k (M.op X1 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10102 X0 X1
       have i₂ := eq7883 X1 X1
       grind)
    | exact superpose eq7883 eq10102
    | (have j0 := eq10102 X0 X1
       grind)
    | exact resolve eq10102 eq7883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7883 eq10102
  have eq10218 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X1 X1)) ∨ (k X0 (k (M.op X1 X1) X1)) = (M.op X0 (k (M.op X1 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10183 X0 X1
       have i₂ := eq6598 X1
       grind)
    | exact superpose eq6598 eq10183
    | (have j0 := eq10183 X0 X1
       grind)
    | exact resolve eq10183 eq6598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6598 eq10183
  have eq10235 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10218 X0 X0
       have i₂ := eq7886 X0
       grind)
    | exact superpose eq7886 eq10218
    | (have j0 := eq10218 X0 X1
       grind)
    | exact resolve eq10218 eq7886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7886 eq10218
  have eq10290 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq135 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq135 X0 X1
       grind)
    | exact superpose eq135 eq12
    | (have j1 := eq135 X1 X0
       grind)
    | exact resolve eq12 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10397 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq10430 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10290 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq10290
    | (have j0 := eq10290 X0 X1
       grind)
    | exact resolve eq10290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10290
  have eq10451 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq10430 X0 X1
       have j1 := eq10397 X1 X0
       grind)
    | (have r₁ := eq10430 X1 X0
       have r₂ := eq10397 X0 X1
       grind)
    | (have r₁ := eq10430 X1 X1
       have r₂ := eq10397 X1 X1
       grind)
    | exact resolve eq10430 eq10397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10397 eq10430
  have eq19170 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7902 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7902
    | exact resolve eq7902 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7902
  have eq19242 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19170 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq19170
    | (have j0 := eq19170 X0 X1
       grind)
    | exact resolve eq19170 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19170
  have eq19252 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19242 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq19242
    | (have j0 := eq19242 X0 X1
       grind)
    | exact resolve eq19242 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19242
  have eq21479 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (τ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq10235 (σ X0) (σ X1)
       grind)
    | exact superpose eq10235 eq15
    | (have j1 := eq10235 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq10235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10235
  have eq21612 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X1 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21479 X0 X1
       have i₂ := eq6942 X1
       grind)
    | exact superpose eq6942 eq21479
    | (have j0 := eq21479 X0 X1
       grind)
    | exact resolve eq21479 eq6942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21479
  have eq21665 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21612 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq21612
    | (have j0 := eq21612 X0 X1
       grind)
    | exact resolve eq21612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21612
  have eq21696 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21665 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21665
    | (have j0 := eq21665 X0 X1
       grind)
    | exact resolve eq21665 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21665
  have eq27027 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4871 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4871
  have eq38926 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq515 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq38929 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38926 X0 X1
       have i₂ := eq6942 X1
       grind)
    | exact superpose eq6942 eq38926
    | (have j0 := eq38926 X0 X1
       grind)
    | exact resolve eq38926 eq6942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38926
  have eq39137 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op X1 X1) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38929 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq38929
    | (have j0 := eq38929 X0 X1
       grind)
    | exact resolve eq38929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38929
  have eq64817 : ∀ X0 X1 X2 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq516 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq516
    | exact resolve eq516 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq65402 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64817 X0 X1 X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq64817
    | (have j0 := eq64817 X0 X1 X2
       grind)
    | exact resolve eq64817 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64817
  have eq65901 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65402 X0 X1 X2
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq65402 X1 X1 X2
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq65402 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65402
  have eq66739 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19252 x y
       grind)
    | exact superpose eq19252 eq16
    | (have j1 := eq19252 x y
       grind)
    | exact resolve eq16 eq19252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67095 : y = (k x y) := by
    first
    | (have j1 := eq1302 x y
       grind)
    | (have r₁ := eq66739
       have r₂ := eq1302 x y
       grind)
    | exact resolve eq66739 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66739
  have eq95131 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21696 x y
       grind)
    | exact superpose eq21696 eq16
    | (have j1 := eq21696 x y
       grind)
    | exact resolve eq16 eq21696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21696
  have eq95531 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq95131
       have i₂ := eq67095
       grind)
    | exact superpose eq67095 eq95131
    | exact resolve eq95131 eq67095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67095 eq95131
  have eq124695 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1796
       have i₂ := eq6914 y x
       grind)
    | exact superpose eq6914 eq1796
    | (have j1 := eq6914 y x
       grind)
    | exact resolve eq1796 eq6914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq124704 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq124695
  have eq124721 : x = (M.op y y) := by
    first
    | (have r₁ := eq124704
       have r₂ := eq95531
       grind)
    | exact resolve eq124704 eq95531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95531 eq124704
  have eq128292 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq9102 y
       have i₂ := eq124721
       grind)
    | exact superpose eq124721 eq9102
    | exact resolve eq9102 eq124721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9102
  have eq128298 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq124721
       grind)
    | exact superpose eq124721 eq9
    | exact resolve eq9 eq124721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128310 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq113 y y X0
       have i₂ := eq124721
       grind)
    | exact superpose eq124721 eq113
    | exact resolve eq113 eq124721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq131106 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq19252 y x
       have i₂ := eq128292
       grind)
    | exact superpose eq128292 eq19252
    | (have j0 := eq19252 y x
       grind)
    | exact resolve eq19252 eq128292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19252
  have eq133915 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10451 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10451
    | exact resolve eq10451 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10451
  have eq133948 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq133915 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq133915
    | (have j0 := eq133915 X0 X1
       grind)
    | exact resolve eq133915 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq133915
  have eq147403 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq133948 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq133948
    | exact resolve eq133948 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133948
  have eq147542 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq147403 X1 X0
       have i₂ := eq244 X0 X1
       grind)
    | (have i₁ := eq147403 (M.op X0 X0) X0
       have i₂ := eq244 X0 X1
       grind)
    | exact superpose eq244 eq147403
    | (have j0 := eq147403 (M.op X0 X0) X0
       have j1 := eq244 X0 X1
       grind)
    | exact resolve eq147403 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq147403
  have eq147604 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq147542 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147542
  have eq156236 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131106
       grind)
    | exact superpose eq131106 eq16
    | exact resolve eq16 eq131106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131106
  have eq156319 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op y x) ∨ y = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq156236
       have i₂ := eq79 X0 x y
       grind)
    | exact superpose eq79 eq156236
    | (have j1 := eq79 y x X0
       grind)
    | (have r₁ := eq156236
       have r₂ := eq79 (σ (M.op x y)) x (σ (k y x))
       grind)
    | (have r₁ := eq156236
       have r₂ := eq79 (σ (k y x)) x (σ (M.op x y))
       grind)
    | exact resolve eq156236 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq156324 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq156236
       have i₂ := eq6914 x y
       grind)
    | exact superpose eq6914 eq156236
    | (have j1 := eq6914 x y
       grind)
    | exact resolve eq156236 eq6914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156325 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq156236
       have i₂ := eq1302 y x
       grind)
    | exact superpose eq1302 eq156236
    | (have j1 := eq1302 y x
       grind)
    | exact resolve eq156236 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302 eq156236
  have eq156330 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (k y x) := by grind
  clear eq156325
  have eq156335 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq156330
       have i₂ := eq128298
       grind)
    | exact superpose eq128298 eq156330
    | exact resolve eq156330 eq128298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156330
  have eq156336 : x = (k y x) := by grind
  clear eq156335
  have eq156337 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq156324
       have i₂ := eq128298
       grind)
    | exact superpose eq128298 eq156324
    | exact resolve eq156324 eq128298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156324
  have eq156338 : x = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq156337
  have eq156347 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ y = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq156319 X0
       have i₂ := eq128298
       grind)
    | exact superpose eq128298 eq156319
    | (have j0 := eq156319 X0
       grind)
    | exact resolve eq156319 eq128298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156319
  have eq156348 : ∀ X0 : G, x = (M.op y x) ∨ y = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq156347 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156347
  have eq156356 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq156338
       have i₂ := eq128298
       grind)
    | exact superpose eq128298 eq156338
    | exact resolve eq156338 eq128298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156338
  have eq156361 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ y = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq156348 X0
       have i₂ := eq128298
       grind)
    | exact superpose eq128298 eq156348
    | (have j0 := eq156348 X0
       grind)
    | exact resolve eq156348 eq128298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156348
  have eq162546 : (σ x) ≠ (σ x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq39137 y x
       have i₂ := eq156336
       grind)
    | exact superpose eq156336 eq39137
    | (have j0 := eq39137 y x
       grind)
    | exact resolve eq39137 eq156336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39137 eq156336
  have eq162548 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq162546
  have eq162551 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq162548
       have i₂ := eq128292
       grind)
    | exact superpose eq128292 eq162548
    | exact resolve eq162548 eq128292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128292 eq162548
  have eq162557 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq162551
       grind)
    | exact superpose eq162551 eq16
    | exact resolve eq16 eq162551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162551
  have eq162730 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) (σ (τ X1))) ∨ (k (σ (τ X0)) X2) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65901 X2 (τ X0) (τ X1)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq65901
    | (have j0 := eq65901 X2 (τ X0) X2
       grind)
    | exact resolve eq65901 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq65901
  have eq162769 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) X1) ∨ (k (σ (τ X0)) X2) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq162730 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq162730
    | (have j0 := eq162730 X0 X1 X2
       grind)
    | exact resolve eq162730 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162730
  have eq162779 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (k (σ (τ X0)) X2) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq162769 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq162769
    | (have j0 := eq162769 X0 X1 X2
       grind)
    | exact resolve eq162769 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162769
  have eq162786 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (k X0 X1) = (k (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq162779 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq162779
    | (have j0 := eq162779 X0 X1 X2
       grind)
    | exact resolve eq162779 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162779
  have eq162788 : (σ x) ≠ (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq162557
       have i₂ := eq156356
       grind)
    | exact superpose eq156356 eq162557
    | exact resolve eq162557 eq156356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156356 eq162557
  have eq162793 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by grind
  clear eq162788
  have eq162794 : y = (M.op x x) := by grind
  clear eq162793
  have eq162840 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq25 x X0
       have i₂ := eq162794
       grind)
    | exact superpose eq162794 eq25
    | exact resolve eq25 eq162794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162928 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq9070 x X0
       have i₂ := eq162794
       grind)
    | exact superpose eq162794 eq9070
    | exact resolve eq9070 eq162794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9070
  have eq162933 : ∀ X0 : G, x ≠ y ∨ (k X0 x) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq27027 X0 x
       have i₂ := eq162794
       grind)
    | exact superpose eq162794 eq27027
    | (have j0 := eq27027 X0 x
       grind)
    | exact resolve eq27027 eq162794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27027
  have eq162937 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq147604 x X0
       have i₂ := eq162794
       grind)
    | exact superpose eq162794 eq147604
    | (have j0 := eq147604 x X0
       grind)
    | exact resolve eq147604 eq162794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147604
  have eq162942 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq25 x x
       have i₂ := eq162794
       grind)
    | exact superpose eq162794 eq25
    | exact resolve eq25 eq162794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq166401 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq128310 X0
       have i₂ := eq162840 X0
       grind)
    | exact superpose eq162840 eq128310
    | exact resolve eq128310 eq162840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162840
  have eq175746 : ∀ X0 X1 : G, (k X0 X1) = (k y X1) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq162786 X0 X1 x
       have i₂ := eq162794
       grind)
    | exact superpose eq162794 eq162786
    | (have j0 := eq162786 X0 X1 x
       grind)
    | exact resolve eq162786 eq162794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162786
  have eq178098 : ∀ X0 : G, y ≠ (k X0 y) ∨ y = (M.op y y) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1081 y
       have i₂ := eq175746 X0 y
       grind)
    | (have i₁ := eq1081 x
       have i₂ := eq175746 x x
       grind)
    | exact superpose eq175746 eq1081
    | (have j0 := eq1081 y
       have j1 := eq175746 X0 x
       grind)
    | exact resolve eq1081 eq175746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq175746
  have eq178269 : ∀ X0 : G, y ≠ (k X0 y) ∨ x = y ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq178098 X0
       have i₂ := eq124721
       grind)
    | exact superpose eq124721 eq178098
    | (have j0 := eq178098 X0
       grind)
    | exact resolve eq178098 eq124721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178098
  have eq182658 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ x = y ∨ (k X0 x) = (M.op X0 x) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq178269 X0
       have i₂ := eq6914 y X0
       grind)
    | exact superpose eq6914 eq178269
    | (have j0 := eq178269 X0
       have j1 := eq6914 y X0
       grind)
    | exact resolve eq178269 eq6914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6914 eq178269
  have eq182692 : ∀ X0 : G, x = X0 ∨ y ≠ (M.op X0 y) ∨ x = y ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq182658 X0
       have i₂ := eq124721
       grind)
    | exact superpose eq124721 eq182658
    | (have j0 := eq182658 X0
       grind)
    | exact resolve eq182658 eq124721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182658
  have eq182702 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ x = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq182692 X0
       have j1 := eq162933 X0
       grind)
    | (have r₁ := eq182692 y
       have r₂ := eq162933 X0
       grind)
    | (have r₁ := eq182692 X0
       have r₂ := eq162933 X0
       grind)
    | exact resolve eq182692 eq162933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162933 eq182692
  have eq184303 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op (M.op x y) x) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq182702 (M.op x y)
       have i₂ := eq162942
       grind)
    | exact superpose eq162942 eq182702
    | (have j0 := eq182702 (M.op x y)
       grind)
    | exact resolve eq182702 eq162942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162942 eq182702
  have eq184308 : x = (M.op x y) ∨ (M.op (M.op x y) x) = (k (M.op x y) x) := by
    first
    | (have j1 := eq156361 (M.op x y)
       grind)
    | (have r₁ := eq184303
       have r₂ := eq156361 (M.op x y)
       grind)
    | exact resolve eq184303 eq156361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156361 eq184303
  have eq184310 : (M.op (M.op x y) x) = (k (M.op x y) x) := by
    first
    | (have j1 := eq162937 (M.op x y)
       grind)
    | (have r₁ := eq184308
       have r₂ := eq162937 x
       grind)
    | exact resolve eq184308 eq162937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162937 eq184308
  have eq184312 : (M.op y (M.op y y)) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq184310
       have i₂ := eq9 y x
       grind)
    | exact superpose eq9 eq184310
    | exact resolve eq184310 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184310
  have eq184314 : (M.op y x) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq184312
       have i₂ := eq124721
       grind)
    | exact superpose eq124721 eq184312
    | exact resolve eq184312 eq124721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124721 eq184312
  have eq184316 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq184314
       have i₂ := eq128298
       grind)
    | exact superpose eq128298 eq184314
    | exact resolve eq184314 eq128298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128298 eq184314
  have eq184942 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1814 (M.op x y) x x
       have i₂ := eq184316
       grind)
    | exact superpose eq184316 eq1814
    | exact resolve eq1814 eq184316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814 eq184316
  have eq184982 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq184942 X0
       have i₂ := eq6942 (M.op x y)
       grind)
    | exact superpose eq6942 eq184942
    | exact resolve eq184942 eq6942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184942
  have eq185064 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (σ (M.op x (M.op x x))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq184982 X0
       have i₂ := eq128310 x
       grind)
    | exact superpose eq128310 eq184982
    | exact resolve eq184982 eq128310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128310 eq184982
  have eq185122 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ x)) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq185064 X0
       have i₂ := eq162794
       grind)
    | exact superpose eq162794 eq185064
    | exact resolve eq185064 eq162794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185064
  have eq185124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq185122 x
       have i₂ := eq162928 x
       grind)
    | exact superpose eq162928 eq185122
    | exact resolve eq185122 eq162928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162928 eq185122
  have eq185125 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq185124
       have r₂ := eq16
       grind)
    | exact resolve eq185124 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185124
  have eq185357 : (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq185125
       grind)
    | exact superpose eq185125 eq10
    | exact resolve eq10 eq185125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185125
  have eq185489 : x = (M.op x y) := by
    first
    | (have i₁ := eq185357
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq185357
    | exact resolve eq185357 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185357
  have eq186073 : (M.op x x) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq166401 x
       have i₂ := eq185489
       grind)
    | exact superpose eq185489 eq166401
    | exact resolve eq166401 eq185489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166401
  have eq186452 : y = (M.op x y) := by
    first
    | (have i₁ := eq186073
       have i₂ := eq162794
       grind)
    | exact superpose eq162794 eq186073
    | exact resolve eq186073 eq162794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162794 eq186073
  have eq186579 : x = y := by
    first
    | (have i₁ := eq186452
       have i₂ := eq185489
       grind)
    | exact superpose eq185489 eq186452
    | exact resolve eq186452 eq185489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185489 eq186452
  have eq187413 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq186579
       grind)
    | exact superpose eq186579 eq16
    | exact resolve eq16 eq186579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186579
  have eq187601 : False := by grind
  exact eq187601

/-- `Equation4386`: `x ◇ (x ◇ x) = (y ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_y_pyx_Equation4386 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4386 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4386.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X1 X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq72 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op X0 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq72 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq72 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq72 (M.op X0 (k X1 X1)) X1
       have r₂ := eq12 X0 (k X1 X1)
       grind)
    | exact resolve eq72 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq102 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op X0 X2) ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 X2
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq24 X0 X1 X2
       have i₂ := eq14 (M.op X2 X1) X1
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X0) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X2 X3 (M.op X3 X1)
       have i₂ := eq24 X3 X1 X0
       grind)
    | (have i₁ := eq24 X2 X3 (M.op X3 X1)
       have i₂ := eq24 X0 X1 X3
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 (M.op X2 X0)
       have i₂ := eq9 X0 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) = (M.op X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X2 X1)
       have i₂ := eq24 X2 X1 X0
       grind)
    | (have i₁ := eq9 X2 (M.op X2 X1)
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op X0 X2) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq102 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq102 X0 (M.op X0 X2) X2
       have r₂ := eq12 (M.op (M.op X0 X2) X2) (M.op X0 X2)
       grind)
    | (have r₁ := eq102 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq102 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq146 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X0)) = (M.op (M.op X2 (M.op X2 X2)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X2 X1
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X0)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 X2
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op X1 (M.op X1 X1))
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X1 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | (have i₁ := eq67 X0 X1
       have i₂ := eq14 (M.op (σ X1) (σ X0)) X1
       grind)
    | exact superpose eq14 eq67
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq67 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq67 X1 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq67 X0 X1
       grind)
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq636 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq622 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq646 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (σ (k X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq565 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq653 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq636 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq636
    | (have j0 := eq636 X0 X1
       grind)
    | exact resolve eq636 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq654 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq653 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq671 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq646 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq646 (M.op X0 (σ X1)) X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq646 (M.op X0 (σ (k X1 X1))) X1
       have r₂ := eq12 X0 (σ (k X1 X1))
       grind)
    | (have r₁ := eq646 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq646 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq1223 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq115 X2 X0 X1
       grind)
    | (have i₁ := eq12 (M.op X1 X2) X1
       have i₂ := eq115 X0 X1 X2
       grind)
    | exact superpose eq115 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq115 X2 X1 X1
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X2) X2) (M.op X0 X2)
       have r₂ := eq115 X0 (M.op X0 X2) X2
       grind)
    | exact resolve eq12 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1274 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1223 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1313 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq1274 (M.op X0 x) X0 X2
       have i₂ := eq114 X0 x X0
       grind)
    | exact superpose eq114 eq1274
    | (have j0 := eq1274 X0 X0 X2
       grind)
    | exact resolve eq1274 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq2062 : ∀ X0 X1 : G, (M.op X0 X0) = (σ X1) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq654 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq654
    | exact resolve eq654 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq2211 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2062 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq2062
    | (have j0 := eq2062 X0 X1
       grind)
    | exact resolve eq2062 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq2539 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2211 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2211
    | exact resolve eq2211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2610 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq2211 X0 X1
       grind)
    | exact superpose eq2211 eq10
    | (have j1 := eq2211 X0 X1
       grind)
    | exact resolve eq10 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211
  have eq3159 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op (M.op X0 X0) X0) X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1274 (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) X0) X1
       have i₂ := eq149 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq149 eq1274
    | (have j0 := eq1274 X0 (M.op (M.op X0 X0) X0) X1
       grind)
    | exact resolve eq1274 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq3196 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3159 X0 X1
       grind)
    | (have r₁ := eq3159 X1 X1
       have r₂ := eq9 X1 X1
       grind)
    | exact resolve eq3159 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3159
  have eq3242 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (k X1 (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3196 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq3196
    | exact resolve eq3196 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196
  have eq4926 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (k X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3242 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq3242
    | exact resolve eq3242 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5247 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq671 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq671
    | (have j0 := eq671 X1 (τ X0)
       grind)
    | exact resolve eq671 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq5346 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5247 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq5247
    | (have j0 := eq5247 X0 X1
       grind)
    | exact resolve eq5247 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq5247
  have eq5354 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5346 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5346
    | (have j0 := eq5346 X0 X1
       grind)
    | exact resolve eq5346 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5346
  have eq5360 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5354 X0 X1
       have j1 := eq76 X1 X0
       grind)
    | (have r₁ := eq5354 X0 X1
       have r₂ := eq76 (k X0 X0) X1
       grind)
    | (have r₁ := eq5354 X0 X0
       have r₂ := eq76 X0 (k X0 X0)
       grind)
    | (have r₁ := eq5354 X0 X1
       have r₂ := eq76 (M.op X0 X1) (k X1 X0)
       grind)
    | exact resolve eq5354 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq5354
  have eq5437 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq5360
  have eq5459 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5437 X0
       have j1 := eq1313 X0 X0
       grind)
    | (have r₁ := eq5437 X0
       have r₂ := eq1313 X0 x
       grind)
    | exact resolve eq5437 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313 eq5437
  have eq5487 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5459 X0
       have j1 := eq1274 X0 X0 X0
       grind)
    | (have r₁ := eq5459 x
       have r₂ := eq1274 x x x
       grind)
    | exact resolve eq5459 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274 eq5459
  have eq5837 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq5487 (σ X0)
       grind)
    | exact superpose eq5487 eq15
    | exact resolve eq15 eq5487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5856 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5837 X0
       have i₂ := eq5487 X0
       grind)
    | exact superpose eq5487 eq5837
    | exact resolve eq5837 eq5487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5487 eq5837
  have eq7957 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2610 (σ X0) X1
       have i₂ := eq5856 X0
       grind)
    | exact superpose eq5856 eq2610
    | (have j0 := eq2610 (σ X0) X1
       grind)
    | exact resolve eq2610 eq5856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2610
  have eq7963 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq5856 X0
       grind)
    | exact superpose eq5856 eq9
    | exact resolve eq9 eq5856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7966 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (σ X0) (σ X0)
       have i₂ := eq5856 X0
       grind)
    | exact superpose eq5856 eq24
    | exact resolve eq24 eq5856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq8029 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7957 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq7957
    | (have j0 := eq7957 X0 X1
       grind)
    | exact resolve eq7957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7957
  have eq8043 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8029 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq8029
    | (have j0 := eq8029 X0 X1
       grind)
    | exact resolve eq8029 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8029
  have eq33872 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8043 x y
       grind)
    | exact superpose eq8043 eq16
    | (have j1 := eq8043 x y
       grind)
    | exact resolve eq16 eq8043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35181 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33872
       have i₂ := eq2539 y x
       grind)
    | exact superpose eq2539 eq33872
    | (have j1 := eq2539 y x
       grind)
    | exact resolve eq33872 eq2539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33872
  have eq35190 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq35181
  have eq35191 : y = (M.op x x) := by grind
  clear eq35190
  have eq35831 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq25 x X0
       have i₂ := eq35191
       grind)
    | exact superpose eq35191 eq25
    | exact resolve eq25 eq35191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq35834 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq105 x X0 X1
       have i₂ := eq35191
       grind)
    | exact superpose eq35191 eq105
    | exact resolve eq105 eq35191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq35836 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X0)) = (M.op (M.op x y) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1 x
       have i₂ := eq35191
       grind)
    | exact superpose eq35191 eq146
    | exact resolve eq146 eq35191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35858 : ∀ X0 : G, (M.op (M.op x y) X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq3242 x x
       have i₂ := eq35191
       grind)
    | exact superpose eq35191 eq3242
    | exact resolve eq3242 eq35191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq35873 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7963 x
       have i₂ := eq35191
       grind)
    | exact superpose eq35191 eq7963
    | exact resolve eq7963 eq35191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7963
  have eq35876 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq9 x x
       have i₂ := eq35191
       grind)
    | exact superpose eq35191 eq9
    | exact resolve eq9 eq35191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35902 : (M.op y (M.op y y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq167 x x
       have i₂ := eq35191
       grind)
    | exact superpose eq35191 eq167
    | exact resolve eq167 eq35191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq48586 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq8043 y x
       have i₂ := eq35873
       grind)
    | exact superpose eq35873 eq8043
    | (have j0 := eq8043 y x
       grind)
    | exact resolve eq8043 eq35873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8043
  have eq152953 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48586
       grind)
    | exact superpose eq48586 eq16
    | exact resolve eq16 eq48586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48586
  have eq153387 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq152953
       have i₂ := eq2539 x y
       grind)
    | exact superpose eq2539 eq152953
    | (have j1 := eq2539 x y
       grind)
    | exact resolve eq152953 eq2539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2539 eq152953
  have eq153395 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op y y) := by grind
  clear eq153387
  have eq153400 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq153395
       have i₂ := eq35876
       grind)
    | exact superpose eq35876 eq153395
    | exact resolve eq153395 eq35876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153395
  have eq153401 : x = (M.op y y) := by grind
  clear eq153400
  have eq153779 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X0)) = (M.op (M.op y x) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1 y
       have i₂ := eq153401
       grind)
    | exact superpose eq153401 eq146
    | exact resolve eq146 eq153401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq153840 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 y y X0 X1
       have i₂ := eq153401
       grind)
    | exact superpose eq153401 eq104
    | exact resolve eq104 eq153401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq154014 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X0)) = (M.op (M.op x y) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq153779 X0 X1
       have i₂ := eq35876
       grind)
    | exact superpose eq35876 eq153779
    | exact resolve eq153779 eq35876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153779
  have eq154083 : ∀ X1 : G, (M.op (M.op x y) (M.op X1 x)) = (M.op (M.op x y) (M.op X1 y)) := by
    intro X1
    first
    | (have i₁ := eq154014 x X1
       have i₂ := eq35836 x X1
       grind)
    | exact superpose eq35836 eq154014
    | exact resolve eq154014 eq35836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35836 eq154014
  have eq157464 : ∀ X0 X1 : G, (M.op (M.op X1 (σ (M.op x y))) X1) = (M.op (σ (M.op (M.op X0 x) X0)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq7966 (M.op x y) X1
       have i₂ := eq153840 X0 x
       grind)
    | exact superpose eq153840 eq7966
    | exact resolve eq7966 eq153840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153840
  have eq157516 : ∀ X1 : G, (M.op (M.op X1 (σ (M.op x y))) X1) = (M.op (σ (M.op x (M.op x x))) (σ (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq157464 x X1
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq157464
    | exact resolve eq157464 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157464
  have eq157834 : ∀ X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op X1 (σ (M.op x y))) X1) := by
    intro X1
    first
    | (have i₁ := eq157516 X1
       have i₂ := eq35191
       grind)
    | exact superpose eq35191 eq157516
    | exact resolve eq157516 eq35191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157516
  have eq157992 : ∀ X1 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op X1 (σ (M.op x y))) X1) := by
    intro X1
    first
    | (have i₁ := eq157834 X1
       have i₂ := eq5856 (M.op x y)
       grind)
    | exact superpose eq5856 eq157834
    | exact resolve eq157834 eq5856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157834
  have eq158062 : ∀ X1 : G, (σ (M.op y (M.op y y))) = (M.op (M.op X1 (σ (M.op x y))) X1) := by
    intro X1
    first
    | (have i₁ := eq157992 X1
       have i₂ := eq35902
       grind)
    | exact superpose eq35902 eq157992
    | exact resolve eq157992 eq35902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35902 eq157992
  have eq158101 : ∀ X1 : G, (σ (M.op y x)) = (M.op (M.op X1 (σ (M.op x y))) X1) := by
    intro X1
    first
    | (have i₁ := eq158062 X1
       have i₂ := eq153401
       grind)
    | exact superpose eq153401 eq158062
    | exact resolve eq158062 eq153401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158062
  have eq158128 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op X1 (σ (M.op x y))) X1) := by
    intro X1
    first
    | (have i₁ := eq158101 X1
       have i₂ := eq35876
       grind)
    | exact superpose eq35876 eq158101
    | exact resolve eq158101 eq35876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35876 eq158101
  have eq161948 : ∀ X1 : G, (k X1 (σ (M.op x y))) = (M.op (σ (M.op x y)) X1) := by
    intro X1
    first
    | (have i₁ := eq4926 X1 (σ (M.op x y)) x
       have i₂ := eq158128 X1
       grind)
    | exact superpose eq158128 eq4926
    | exact resolve eq4926 eq158128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4926
  have eq163260 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (M.op x y)
       have i₂ := eq161948 (σ X0)
       grind)
    | exact superpose eq161948 eq15
    | exact resolve eq15 eq161948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161948
  have eq163284 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ X0)) = (σ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq163260 X0
       have i₂ := eq35858 X0
       grind)
    | exact superpose eq35858 eq163260
    | exact resolve eq163260 eq35858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35858 eq163260
  have eq174533 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ X0) x)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq35834 (σ (M.op x y)) (σ X0)
       have i₂ := eq163284 X0
       grind)
    | exact superpose eq163284 eq35834
    | exact resolve eq35834 eq163284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35834 eq163284
  have eq190961 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) X0) = (M.op (σ (M.op (M.op x y) (M.op x x))) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq7966 (M.op x y) X0
       have i₂ := eq154083 x
       grind)
    | exact superpose eq154083 eq7966
    | exact resolve eq7966 eq154083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7966 eq154083
  have eq191016 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) X0) = (M.op (M.op x y) (M.op (σ (M.op x x)) x)) := by
    intro X0
    first
    | (have i₁ := eq190961 X0
       have i₂ := eq174533 (M.op x x)
       grind)
    | exact superpose eq174533 eq190961
    | exact resolve eq190961 eq174533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174533 eq190961
  have eq191085 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) X0) = (M.op (M.op x y) (M.op (σ y) x)) := by
    intro X0
    first
    | (have i₁ := eq191016 X0
       have i₂ := eq35191
       grind)
    | exact superpose eq35191 eq191016
    | exact resolve eq191016 eq35191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35191 eq191016
  have eq191133 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) X0) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq191085 X0
       have i₂ := eq35831 (σ y)
       grind)
    | exact superpose eq35831 eq191085
    | exact resolve eq191085 eq35831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35831 eq191085
  have eq191168 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) X0) = (M.op (σ y) (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq191133 X0
       have i₂ := eq5856 y
       grind)
    | exact superpose eq5856 eq191133
    | exact resolve eq191133 eq5856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5856 eq191133
  have eq191200 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (σ (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq191168 X0
       have i₂ := eq153401
       grind)
    | exact superpose eq153401 eq191168
    | exact resolve eq191168 eq153401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153401 eq191168
  have eq191219 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq191200 x
       have i₂ := eq158128 x
       grind)
    | exact superpose eq158128 eq191200
    | exact resolve eq191200 eq158128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158128 eq191200
  have eq191285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35873
       have i₂ := eq191219
       grind)
    | exact superpose eq191219 eq35873
    | exact resolve eq35873 eq191219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35873 eq191219
  have eq191510 : False := by grind
  exact eq191510

/-- `Equation4388`: `x ◇ (x ◇ x) = (y ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_y_pxy_Equation4388 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4388 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4388.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq71 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq88 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq138 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) = (M.op X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1)
       have i₂ := eq25 X1 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq9 X2 (M.op X1 X1)
       have i₂ := eq25 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq88 (σ X1) (σ X0)
       grind)
    | exact superpose eq88 eq15
    | (have j1 := eq88 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq88 X1 (τ X0)
       grind)
    | exact superpose eq88 eq19
    | (have j1 := eq88 X1 (τ X0)
       grind)
    | exact resolve eq19 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq162 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq88
  have eq201 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq162 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq202 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq201 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq253 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq202 (σ X0)
       grind)
    | exact superpose eq202 eq15
    | exact resolve eq15 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq202 (τ X0)
       grind)
    | exact superpose eq202 eq35
    | exact resolve eq35 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq255 X0
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq255
    | exact resolve eq255 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq260 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq253 X0
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq253
    | exact resolve eq253 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq253
  have eq322 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (τ X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq258 X0
       grind)
    | exact superpose eq258 eq9
    | exact resolve eq9 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq258
  have eq340 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq326 X0
       have i₂ := eq35 (M.op X0 X0) X0
       grind)
    | exact superpose eq35 eq326
    | exact resolve eq326 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq326
  have eq343 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq340
  have eq452 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq260 X0
       grind)
    | exact superpose eq260 eq9
    | exact resolve eq9 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 X2 (σ X0)
       have i₂ := eq260 X0
       grind)
    | exact superpose eq260 eq25
    | exact resolve eq25 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1593 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ (σ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq452 (σ X0) X1
       have i₂ := eq260 X0
       grind)
    | exact superpose eq260 eq452
    | exact resolve eq452 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1906 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (σ (σ (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq458 (σ X0) X1 X2
       have i₂ := eq260 X0
       grind)
    | exact superpose eq260 eq458
    | exact resolve eq458 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5466 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ (σ (σ (M.op X0 X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1593 (σ X0) X1
       have i₂ := eq260 X0
       grind)
    | exact superpose eq260 eq1593
    | exact resolve eq1593 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq5824 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (σ (σ (σ (M.op X0 X0)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1906 (σ X0) X1 X2
       have i₂ := eq260 X0
       grind)
    | exact superpose eq260 eq1906
    | exact resolve eq1906 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906
  have eq7590 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (τ X0)) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq322 X0 X1
       have i₂ := eq343 X0
       grind)
    | exact superpose eq343 eq322
    | exact resolve eq322 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq343
  have eq7821 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X0) X1)) = (M.op (M.op X2 X2) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7590 X1 X2
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq7590
    | exact resolve eq7590 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7590
  have eq8613 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (τ (M.op (M.op X1 X1) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7821 X1 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7821
    | exact resolve eq7821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7821
  have eq9435 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq154 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq154
    | exact resolve eq154 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq9674 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9435 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9435
    | (have j0 := eq9435 X0 X1
       grind)
    | exact resolve eq9435 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9435
  have eq9920 : ∀ X0 X1 X3 : G, (τ (M.op (M.op X0 X0) (σ X1))) = (M.op (σ (M.op X3 X3)) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq458 X3 x X1
       have i₂ := eq8613 X1 X0 x
       grind)
    | exact superpose eq8613 eq458
    | exact resolve eq458 eq8613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9934 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (τ (M.op (M.op X0 X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq138 x x X1
       have i₂ := eq8613 X1 X0 (M.op x x)
       grind)
    | exact superpose eq8613 eq138
    | exact resolve eq138 eq8613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10046 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op (M.op X2 X2) (σ X1))
       have i₂ := eq8613 X1 X2 X0
       grind)
    | exact superpose eq8613 eq11
    | exact resolve eq11 eq8613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8613
  have eq13003 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (M.op X1 X1) (σ X0))
       have i₂ := eq9934 X1 X0
       grind)
    | exact superpose eq9934 eq11
    | exact resolve eq11 eq9934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9934
  have eq14157 : ∀ X0 X2 : G, (σ (M.op X0 (M.op X0 X0))) = (σ (M.op (M.op X2 X2) X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq10046 X2 X0 x
       have i₂ := eq13003 X0 x
       grind)
    | exact superpose eq13003 eq10046
    | exact resolve eq10046 eq13003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10046 eq13003
  have eq15695 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq152 X1 X0
       grind)
    | exact superpose eq152 eq10
    | (have j1 := eq152 X1 X0
       grind)
    | exact resolve eq10 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq15950 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15695 X0 X1
       have i₂ := eq260 X0
       grind)
    | exact superpose eq260 eq15695
    | (have j0 := eq15695 X0 X1
       grind)
    | exact resolve eq15695 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq15695
  have eq16154 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15950 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq15950
    | (have j0 := eq15950 X0 X1
       grind)
    | exact resolve eq15950 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15950
  have eq18579 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X1 X1))) = (σ (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14157 X1 x
       have i₂ := eq458 X0 x X1
       grind)
    | exact superpose eq458 eq14157
    | exact resolve eq14157 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458 eq14157
  have eq182466 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16154 y x
       grind)
    | exact superpose eq16154 eq16
    | (have j1 := eq16154 y x
       grind)
    | exact resolve eq16 eq16154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16154
  have eq183265 : x = (M.op y y) := by
    first
    | (have j1 := eq9674 x y
       grind)
    | (have r₁ := eq182466
       have r₂ := eq9674 x y
       grind)
    | exact resolve eq182466 eq9674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9674 eq182466
  have eq185025 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq183265
       grind)
    | exact superpose eq183265 eq9
    | exact resolve eq9 eq183265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185029 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1 y
       have i₂ := eq183265
       grind)
    | exact superpose eq183265 eq25
    | exact resolve eq25 eq183265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq185050 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op x (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq138 y X0 X1
       have i₂ := eq183265
       grind)
    | exact superpose eq183265 eq138
    | exact resolve eq138 eq183265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq185080 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq452 y X0
       have i₂ := eq183265
       grind)
    | exact superpose eq183265 eq452
    | exact resolve eq452 eq183265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq185126 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) X0) = (τ (M.op x (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9920 y X0 X1
       have i₂ := eq183265
       grind)
    | exact superpose eq183265 eq9920
    | exact resolve eq9920 eq183265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9920 eq183265
  have eq185211 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 X0)) X1) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq185050 X0 X1
       have i₂ := eq185080 X1
       grind)
    | exact superpose eq185080 eq185050
    | exact resolve eq185050 eq185080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185050 eq185080
  have eq193822 : ∀ X0 X1 : G, (M.op (σ (σ (σ (M.op X1 X1)))) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5466 X1 X0
       have i₂ := eq185025 X0
       grind)
    | exact superpose eq185025 eq5466
    | exact resolve eq5466 eq185025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5466
  have eq193840 : ∀ X0 X1 : G, (σ (M.op (σ (M.op X1 X1)) X0)) = (σ (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18579 X1 X0
       have i₂ := eq185025 X0
       grind)
    | exact superpose eq185025 eq18579
    | exact resolve eq18579 eq185025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18579 eq185025
  have eq193920 : ∀ X0 : G, (σ (M.op x X0)) = (σ (τ (M.op x (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq193840 X0 x
       have i₂ := eq185126 X0 x
       grind)
    | exact superpose eq185126 eq193840
    | exact resolve eq193840 eq185126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185126 eq193840
  have eq194014 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq193920 X0
       have i₂ := eq11 (M.op x (σ X0))
       grind)
    | exact superpose eq11 eq193920
    | exact resolve eq193920 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193920
  have eq197882 : ∀ X0 X1 X2 : G, (M.op (σ (σ (σ (M.op X2 X2)))) X1) = (M.op (M.op x (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5824 X2 (M.op X0 X0) X1
       have i₂ := eq185029 X0 (M.op X0 X0)
       grind)
    | exact superpose eq185029 eq5824
    | exact resolve eq5824 eq185029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5824 eq185029
  have eq198107 : ∀ X1 X2 : G, (M.op (σ (σ (σ (M.op X2 X2)))) X1) = (M.op (σ x) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq197882 x X1 X2
       have i₂ := eq185211 x X1
       grind)
    | exact superpose eq185211 eq197882
    | exact resolve eq197882 eq185211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185211 eq197882
  have eq198352 : ∀ X1 : G, (M.op x X1) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq198107 X1 x
       have i₂ := eq193822 X1 x
       grind)
    | exact superpose eq193822 eq198107
    | exact resolve eq198107 eq193822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193822 eq198107
  have eq203010 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq198352 (σ y)
       grind)
    | exact superpose eq198352 eq16
    | exact resolve eq16 eq198352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198352
  have eq203381 : False := by grind
  exact eq203381

/-- `Equation4388`: `x ◇ (x ◇ x) = (y ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_y_pyx_Equation4388 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4388 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4388.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq44 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq48 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq44
    | (have j0 := eq44 X0
       grind)
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq49 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq43
    | (have j0 := eq43 X0
       grind)
    | exact resolve eq43 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq73 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op (M.op X1 X1) X2) ∨ (M.op X0 X0) = X3 ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X1 X2 X3
       have i₂ := eq14 X3 X0
       grind)
    | (have i₁ := eq25 X0 X1 X2
       have i₂ := eq14 X0 (M.op X2 X2)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X3 X0
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq397 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq48 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq401 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq397 X0
       have j1 := eq49 X0
       grind)
    | (have r₁ := eq397 X0
       have r₂ := eq49 X0
       grind)
    | exact resolve eq397 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq397
  have eq416 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq24 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq401 (σ X0)
       grind)
    | exact superpose eq401 eq24
    | exact resolve eq24 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq419 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq416 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq416
    | exact resolve eq416 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq491 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq71 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq7474 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X2 X1) ∨ (M.op X2 X2) = X1 ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X2 X2) = X1 ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq491 X1 X2
       have i₂ := eq73 X2 X1 X0
       grind)
    | (have i₁ := eq491 (M.op X2 X2) X1
       have i₂ := eq73 X0 X1 X2
       grind)
    | exact superpose eq73 eq491
    | (have j0 := eq491 X1 X2
       have j1 := eq73 X2 X1 X2
       grind)
    | (have r₁ := eq491 X1 (M.op X2 X2)
       have r₂ := eq73 (M.op X2 X2) X1 X2
       grind)
    | (have r₁ := eq491 (M.op X2 X2) X1
       have r₂ := eq73 (M.op X2 X2) X1 X2
       grind)
    | (have r₁ := eq491 X0 X0
       have r₂ := eq73 X0 (M.op X0 X0) X2
       grind)
    | exact resolve eq491 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq491
  have eq7576 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X2 X1) ∨ (M.op X2 X2) = X1 ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq7474 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7474
  have eq7609 : ∀ X1 X2 : G, (M.op X2 X2) = X1 ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X1 X2
    first
    | (have j0 := eq7576 x X1 X2
       have j1 := eq114 X2 X1 X2 X1
       grind)
    | (have r₁ := eq7576 x X2 (M.op X1 X1)
       have r₂ := eq114 (M.op x x) X1 X2 x
       grind)
    | (have r₁ := eq7576 X1 X2 x
       have r₂ := eq114 x X1 X2 x
       grind)
    | (have r₁ := eq7576 x (M.op x x) X2
       have r₂ := eq114 (M.op x x) X1 X2 (M.op X2 (M.op x x))
       grind)
    | exact resolve eq7576 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq7576
  have eq7676 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq7736 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq401 X1
       have i₂ := eq7609 X0 X1
       grind)
    | (have i₁ := eq401 X0
       have i₂ := eq7609 (M.op X0 X0) x
       grind)
    | exact superpose eq7609 eq401
    | (have j1 := eq7609 X0 X1
       grind)
    | exact resolve eq401 eq7609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq7771 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq419 X1
       have i₂ := eq7609 X0 (σ X1)
       grind)
    | (have i₁ := eq419 X0
       have i₂ := eq7609 (M.op (σ X0) (σ X0)) x
       grind)
    | exact superpose eq7609 eq419
    | (have j1 := eq7609 X0 (σ X1)
       grind)
    | exact resolve eq419 eq7609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq8053 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7736 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8972 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7676 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7676
  have eq8973 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8972 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8972
  have eq9326 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq8973 (σ X0)
       grind)
    | exact superpose eq8973 eq15
    | exact resolve eq15 eq8973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9345 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9326 X0
       have i₂ := eq8973 X0
       grind)
    | exact superpose eq8973 eq9326
    | exact resolve eq9326 eq8973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8973 eq9326
  have eq11017 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq11088 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7609 X1 (σ X0)
       have i₂ := eq9345 X0
       grind)
    | exact superpose eq9345 eq7609
    | (have j0 := eq7609 X1 (σ X0)
       grind)
    | exact resolve eq7609 eq9345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9345
  have eq11137 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11017 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq11017
    | exact resolve eq11017 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11017
  have eq11157 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq11137
  have eq192304 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7771 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7771
    | (have j0 := eq7771 (σ X0) X1
       grind)
    | exact resolve eq7771 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7771
  have eq192617 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq192304 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq192304
    | (have j0 := eq192304 X0 X1
       grind)
    | exact resolve eq192304 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192304
  have eq202531 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq192617 y x
       grind)
    | exact superpose eq192617 eq16
    | (have j1 := eq192617 y x
       grind)
    | exact resolve eq16 eq192617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192617
  have eq204642 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq202531
       have i₂ := eq7609 y x
       grind)
    | exact superpose eq7609 eq202531
    | (have j1 := eq7609 y x
       grind)
    | exact resolve eq202531 eq7609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7609
  have eq204645 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq202531
       have i₂ := eq7736 y x
       grind)
    | exact superpose eq7736 eq202531
    | (have j1 := eq7736 y x
       grind)
    | exact resolve eq202531 eq7736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7736 eq202531
  have eq204651 : x = (M.op x y) ∨ x = (k y x) := by grind
  clear eq204645
  have eq204653 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq204642
  have eq204697 : x = (k y x) := by
    first
    | (have j1 := eq8053 y x
       grind)
    | (have r₁ := eq204651
       have r₂ := eq8053 y x
       grind)
    | exact resolve eq204651 eq8053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8053 eq204651
  have eq221529 : ∀ X0 X1 : G, (M.op X1 X1) = (τ X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq11088 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq11088 X0 (σ X0)
       grind)
    | exact superpose eq11088 eq10
    | (have j1 := eq11088 X1 X0
       grind)
    | exact resolve eq10 eq11088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11088
  have eq232359 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq221529 (σ X1) X0
       grind)
    | exact superpose eq221529 eq15
    | (have j1 := eq221529 (σ X1) X0
       grind)
    | exact resolve eq15 eq221529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221529
  have eq232363 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq232359 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq232359
    | (have j0 := eq232359 X0 X1
       grind)
    | exact resolve eq232359 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232359
  have eq251309 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq232363 x y
       grind)
    | exact superpose eq232363 eq16
    | (have j1 := eq232363 x y
       grind)
    | exact resolve eq16 eq232363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232363
  have eq251576 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq251309
       have i₂ := eq204697
       grind)
    | exact superpose eq204697 eq251309
    | exact resolve eq251309 eq204697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204697 eq251309
  have eq253811 : (σ x) ≠ (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq251576
       have i₂ := eq204653
       grind)
    | exact superpose eq204653 eq251576
    | exact resolve eq251576 eq204653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204653 eq251576
  have eq253812 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by grind
  clear eq253811
  have eq253813 : y = (M.op x x) := by grind
  clear eq253812
  have eq255131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11157 x
       have i₂ := eq253813
       grind)
    | exact superpose eq253813 eq11157
    | exact resolve eq11157 eq253813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11157 eq253813
  have eq255290 : False := by grind
  exact eq255290

/-- `Equation4389`: `x ◇ (x ◇ x) = (y ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_pxx_x_pxy_Equation4389 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4389 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4389.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
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
  have eq24 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X2 X2) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq9 x X2
       have i₂ := eq9 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq9 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X1) = (k X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X1 X1)
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op X1 X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq19
    | exact resolve eq19 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq40
    | exact resolve eq40 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq40
  have eq46 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq47 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq46
    | (have j0 := eq46 X0
       grind)
    | exact resolve eq46 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq48 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ X0) (M.op (τ X0) (τ X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq47
    | (have j0 := eq47 X0
       grind)
    | exact resolve eq47 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
       have r₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq119 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq24
    | exact resolve eq24 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq10
    | exact resolve eq10 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ X1 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X1 X1) X1) ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 (M.op X0 X0) X0
       have i₂ := eq24 X0 x
       grind)
    | (have i₁ := eq73 (M.op x x) x
       have i₂ := eq24 X0 x
       grind)
    | exact superpose eq24 eq73
    | (have j0 := eq73 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq73 (M.op (M.op (M.op x x) x) (M.op (M.op x x) x)) (M.op (M.op x x) x)
       have r₂ := eq24 (M.op (M.op x x) x) x
       grind)
    | (have r₁ := eq73 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)
       have r₂ := eq24 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq73 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq191 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X1 X1) = (k X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq34
    | (have j0 := eq34 X0 X1
       grind)
    | exact resolve eq34 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq201 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq9
    | exact resolve eq9 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq24
    | exact resolve eq24 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq262 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq259 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq259 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq259 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq259 X0 X1
       have r₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact resolve eq259 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq317 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1
       have i₂ := eq262 (σ X1) X0
       grind)
    | (have i₁ := eq42 X0
       have i₂ := eq262 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq262 eq42
    | (have j1 := eq262 (σ X1) X0
       grind)
    | exact resolve eq42 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 X1 : G, (M.op X1 X1) = (σ X0) ∨ (k (τ X1) X0) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1
       have i₂ := eq262 (τ X1) X0
       grind)
    | (have i₁ := eq44 X0
       have i₂ := eq262 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq262 eq44
    | (have j1 := eq262 (τ X1) X0
       grind)
    | exact resolve eq44 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq835 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (M.op (τ X1) (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq201 X1 (τ X0)
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq201
    | exact resolve eq201 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : ∀ X0 X2 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op (τ X2) (τ (M.op X2 X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq201 X2 x
       have i₂ := eq201 X0 x
       grind)
    | exact superpose eq201 eq201
    | exact resolve eq201 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1809 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (τ X0) (τ X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq25
    | (have j1 := eq48 X0
       grind)
    | exact resolve eq25 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1829 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (τ (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1809 X0 X1
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq1809
    | (have j0 := eq1809 X0 X1
       grind)
    | exact resolve eq1809 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq2263 : ∀ X0 X1 : G, (M.op X1 X1) = (τ X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq317 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq317 (σ X0) X1
       grind)
    | exact superpose eq317 eq10
    | (have j1 := eq317 X0 X1
       grind)
    | exact resolve eq10 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq2527 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X0)
       have i₂ := eq319 (τ X1) X0
       grind)
    | exact superpose eq319 eq19
    | (have j1 := eq319 (τ X1) X0
       grind)
    | exact resolve eq19 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq319
  have eq2531 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2527 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2527
    | (have j0 := eq2527 X0 X1
       grind)
    | exact resolve eq2527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq2559 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2531 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2531
    | (have j0 := eq2531 X0 X1
       grind)
    | exact resolve eq2531 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531
  have eq6362 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) ∨ (M.op (M.op X0 X0) X0) = (k (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq164 X0 (M.op (M.op X0 X0) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq6769 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2263 (σ X1) X0
       grind)
    | exact superpose eq2263 eq15
    | (have j1 := eq2263 (σ X1) X0
       grind)
    | exact resolve eq15 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq6804 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6769 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq6769
    | (have j0 := eq6769 X0 X1
       grind)
    | exact resolve eq6769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6769
  have eq14701 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6804 x y
       grind)
    | exact superpose eq6804 eq16
    | (have j1 := eq6804 x y
       grind)
    | exact resolve eq16 eq6804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6804
  have eq15695 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14701
       have i₂ := eq262 x y
       grind)
    | exact superpose eq262 eq14701
    | (have j1 := eq262 x y
       grind)
    | exact resolve eq14701 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq14701
  have eq15698 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq15695
  have eq15699 : y = (M.op x x) := by grind
  clear eq15698
  have eq16248 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq15699
       grind)
    | exact superpose eq15699 eq9
    | exact resolve eq9 eq15699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16252 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq24 X0 x
       have i₂ := eq15699
       grind)
    | exact superpose eq15699 eq24
    | exact resolve eq24 eq15699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq16254 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25 X0 x
       have i₂ := eq15699
       grind)
    | exact superpose eq15699 eq25
    | exact resolve eq25 eq15699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq16258 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq119 x X0
       have i₂ := eq15699
       grind)
    | exact superpose eq15699 eq119
    | exact resolve eq119 eq15699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16267 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (τ x) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq201 x X0
       have i₂ := eq15699
       grind)
    | exact superpose eq15699 eq201
    | exact resolve eq201 eq15699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq16269 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (τ y) (τ x)) := by
    intro X0
    first
    | (have i₁ := eq207 x X0
       have i₂ := eq15699
       grind)
    | exact superpose eq15699 eq207
    | exact resolve eq207 eq15699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16298 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op (τ y) (τ x)) := by
    intro X0
    first
    | (have i₁ := eq835 x X0
       have i₂ := eq15699
       grind)
    | exact superpose eq15699 eq835
    | exact resolve eq835 eq15699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq16300 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op (τ x) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq842 X0 x
       have i₂ := eq15699
       grind)
    | exact superpose eq15699 eq842
    | exact resolve eq842 eq15699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842 eq15699
  have eq16327 : (M.op (τ x) (τ y)) = (M.op (τ y) (τ x)) := by
    first
    | (have i₁ := eq16298 x
       have i₂ := eq16300 x
       grind)
    | exact superpose eq16300 eq16298
    | exact resolve eq16298 eq16300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16298 eq16300
  have eq16330 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16248 x
       have i₂ := eq16254 x
       grind)
    | exact superpose eq16254 eq16248
    | exact resolve eq16248 eq16254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16248
  have eq17362 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq119 X1 x
       have i₂ := eq16252 x
       grind)
    | exact superpose eq16252 eq119
    | exact resolve eq119 eq16252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq17367 : ∀ X1 : G, (M.op (τ (M.op X1 X1)) (τ X1)) = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq207 X1 x
       have i₂ := eq16252 x
       grind)
    | exact superpose eq16252 eq207
    | exact resolve eq207 eq16252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq16252
  have eq17423 : ∀ X1 : G, (M.op x y) = (M.op (τ (M.op X1 X1)) (τ X1)) := by
    intro X1
    first
    | (have i₁ := eq17367 X1
       have i₂ := eq16330
       grind)
    | exact superpose eq16330 eq17367
    | exact resolve eq17367 eq16330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17367
  have eq17426 : ∀ X1 : G, (M.op x y) = (M.op (σ X1) (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq17362 X1
       have i₂ := eq16330
       grind)
    | exact superpose eq16330 eq17362
    | exact resolve eq17362 eq16330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16330 eq17362
  have eq18150 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq9 x X1
       have i₂ := eq16254 x
       grind)
    | exact superpose eq16254 eq9
    | exact resolve eq9 eq16254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22290 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18150 x
       have i₂ := eq16258 x
       grind)
    | exact superpose eq16258 eq18150
    | exact resolve eq18150 eq16258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16258
  have eq23237 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22290
       grind)
    | exact superpose eq22290 eq16
    | exact resolve eq16 eq22290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22290
  have eq28345 : (M.op x y) = (M.op (τ x) (τ y)) := by
    first
    | (have i₁ := eq18150 x
       have i₂ := eq16267 x
       grind)
    | exact superpose eq16267 eq18150
    | exact resolve eq18150 eq16267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16267 eq18150
  have eq31192 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (M.op X0 X0))) ∨ (k X1 (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1)
       have i₂ := eq1829 X1 X0
       grind)
    | exact superpose eq1829 eq11
    | (have j1 := eq1829 X1 X1
       grind)
    | exact resolve eq11 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31268 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (M.op X1 (M.op X1 X1)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq1829 (τ X0) X1
       grind)
    | exact superpose eq1829 eq18
    | (have j1 := eq1829 (τ X0) X1
       grind)
    | exact resolve eq18 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829
  have eq31276 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X1 (M.op X1 X1)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31268 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq31268
    | (have j0 := eq31268 X0 X1
       grind)
    | exact resolve eq31268 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31268
  have eq31336 : ∀ X1 : G, (k X1 (M.op X1 X1)) = X1 ∨ (M.op X1 X1) = (σ (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq31192 x X1
       have i₂ := eq16254 x
       grind)
    | exact superpose eq16254 eq31192
    | (have j0 := eq31192 x X1
       grind)
    | exact resolve eq31192 eq16254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31192
  have eq31438 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X1 (M.op X1 X1)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31276 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31276
    | (have j0 := eq31276 X0 X1
       grind)
    | exact resolve eq31276 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31276
  have eq31540 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (τ (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31438 X0 X1
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq31438
    | (have j0 := eq31438 X0 X1
       grind)
    | exact resolve eq31438 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31438
  have eq31614 : ∀ X0 : G, (M.op x y) = (τ (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq31540 X0 x
       have i₂ := eq16254 x
       grind)
    | exact superpose eq16254 eq31540
    | (have j0 := eq31540 X0 x
       grind)
    | exact resolve eq31540 eq16254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16254 eq31540
  have eq147682 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ (M.op x y)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq31336 (τ X0)
       grind)
    | exact superpose eq31336 eq18
    | (have j1 := eq31336 (τ X0)
       grind)
    | exact resolve eq18 eq31336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31336
  have eq147777 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (σ (M.op x y)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq147682 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq147682
    | (have j0 := eq147682 X0
       grind)
    | exact resolve eq147682 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147682
  have eq147844 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ (M.op x y)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq147777 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq147777
    | (have j0 := eq147777 X0
       grind)
    | exact resolve eq147777 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147777
  have eq147900 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ (M.op x y)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq147844 X0
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq147844
    | (have j0 := eq147844 X0
       grind)
    | exact resolve eq147844 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147844
  have eq259396 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ (M.op x y)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq147900 (τ X0)
       grind)
    | exact superpose eq147900 eq18
    | (have j1 := eq147900 (τ X0)
       grind)
    | exact resolve eq18 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq147900
  have eq259420 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (σ (M.op x y)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq259396 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq259396
    | (have j0 := eq259396 X0
       grind)
    | exact resolve eq259396 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq259396
  have eq259436 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ (M.op x y)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq259420 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq259420
    | (have j0 := eq259420 X0
       grind)
    | exact resolve eq259420 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259420
  have eq259448 : ∀ X0 : G, (σ (M.op x y)) = (τ (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq259436 X0
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq259436
    | (have j0 := eq259436 X0
       grind)
    | exact resolve eq259436 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq259436
  have eq506395 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq31614 X0
       have i₂ := eq259448 X0
       grind)
    | exact superpose eq259448 eq31614
    | (have j0 := eq31614 X0
       have j1 := eq259448 X0
       grind)
    | exact resolve eq31614 eq259448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31614 eq259448
  have eq506409 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq506395 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506395
  have eq506417 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq506409 X0
       grind)
    | (have r₁ := eq506409 X0
       have r₂ := eq23237
       grind)
    | exact resolve eq506409 eq23237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506409
  have eq508783 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq506417 X1
       have i₂ := eq2559 X1 X0
       grind)
    | (have i₁ := eq506417 X0
       have i₂ := eq2559 X0 (M.op X0 X0)
       grind)
    | exact superpose eq2559 eq506417
    | (have j1 := eq2559 X1 X0
       grind)
    | exact resolve eq506417 eq2559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559 eq506417
  have eq537074 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq508783 X0 (M.op X0 X0)
       have i₂ := eq17423 X0
       grind)
    | exact superpose eq17423 eq508783
    | (have j0 := eq508783 X0 (M.op X0 X0)
       grind)
    | exact resolve eq508783 eq17423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17423 eq508783
  have eq581496 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (σ (M.op X1 X1)) (σ X1)) ∨ (M.op (M.op X0 X0) X0) = (k (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) ∨ (M.op (M.op X0 X0) X0) = (k (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       have i₂ := eq6362 X0
       grind)
    | exact superpose eq6362 eq191
    | (have j1 := eq6362 X0
       grind)
    | exact resolve eq191 eq6362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq6362
  have eq582001 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (σ (M.op X1 X1)) (σ X1)) ∨ (M.op (M.op X0 X0) X0) = (k (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq581496 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581496
  have eq582010 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq582001 X0 x
       grind)
    | (have r₁ := eq582001 x X0
       have r₂ := eq125 X0 x
       grind)
    | exact resolve eq582001 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq582001
  have eq582014 : (M.op (τ y) (τ x)) = (k (M.op (M.op (τ y) (τ x)) (M.op (τ y) (τ x))) (M.op (τ y) (τ x))) := by
    first
    | (have i₁ := eq582010 x
       have i₂ := eq16269 x
       grind)
    | exact superpose eq16269 eq582010
    | exact resolve eq582010 eq16269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16269 eq582010
  have eq582018 : (M.op (τ x) (τ y)) = (k (M.op (M.op (τ x) (τ y)) (M.op (τ x) (τ y))) (M.op (τ x) (τ y))) := by
    first
    | (have i₁ := eq582014
       have i₂ := eq16327
       grind)
    | exact superpose eq16327 eq582014
    | exact resolve eq582014 eq16327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16327 eq582014
  have eq582022 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq582018
       have i₂ := eq28345
       grind)
    | exact superpose eq28345 eq582018
    | exact resolve eq582018 eq28345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28345 eq582018
  have eq2292426 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq537074 (M.op x y)
       have i₂ := eq582022
       grind)
    | exact superpose eq582022 eq537074
    | exact resolve eq537074 eq582022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537074 eq582022
  have eq2292431 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq2292426
       have r₂ := eq23237
       grind)
    | exact resolve eq2292426 eq23237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2292426
  have eq2292614 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq17426 (M.op x y)
       have i₂ := eq2292431
       grind)
    | exact superpose eq2292431 eq17426
    | exact resolve eq17426 eq2292431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17426
  have eq2292703 : (M.op x y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2292614
       have i₂ := eq42 (M.op x y)
       grind)
    | exact superpose eq42 eq2292614
    | exact resolve eq2292614 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2292614
  have eq2292855 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq2292703
       have i₂ := eq2292431
       grind)
    | exact superpose eq2292431 eq2292703
    | exact resolve eq2292703 eq2292431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2292431 eq2292703
  have eq2292955 : False := by grind
  exact eq2292955
