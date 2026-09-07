import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation417`: `x = x ◇ (x ◇ (y ◇ (x ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_Equation417 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law417 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law417.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq207 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
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
  have eq234 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq207
    | (have j0 := eq207 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq594 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
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
  have eq634 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq594
       have i₂ := eq234 x y
       grind)
    | exact superpose eq234 eq594
    | (have j1 := eq234 (σ x) (σ y)
       grind)
    | (have r₁ := eq594
       have r₂ := eq234 x y
       grind)
    | (have r₁ := eq594
       have r₂ := eq234 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq594
       have r₂ := eq234 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq594 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq594
  have eq635 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq634
  have eq723 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq635
       grind)
    | exact superpose eq635 eq10
    | exact resolve eq10 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq758 : x = y ∨ x = y := by
    first
    | (have i₁ := eq723
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq723
    | exact resolve eq723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq759 : x = y := by grind
  clear eq758
  have eq783 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq759
       grind)
    | exact superpose eq759 eq16
    | exact resolve eq16 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq784 : False := by grind
  exact eq784

/-- `Equation417`: `x = x ◇ (x ◇ (y ◇ (x ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation417 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law417 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law417.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq47 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X2) = (k X1 X2) ∨ X1 = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ X0 = X2 := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ X0 = X2 := by
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
  have eq60 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq47 X1 X1 X2
       have j1 := eq56 X1 X1 X2
       grind)
    | (have r₁ := eq47 X0 X1 X2
       have r₂ := eq56 X0 X1 X2
       grind)
    | (have r₁ := eq47 X1 X0 X2
       have r₂ := eq56 X0 X1 X2
       grind)
    | (have r₁ := eq47 X0 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq56 X0 X1 X2
       grind)
    | exact resolve eq47 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq56
  have eq147 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq148 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq147 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq149 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq187 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq149 (σ X0) (σ X1)
       grind)
    | exact superpose eq149 eq15
    | (have j1 := eq149 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq149 (τ X0) X1
       grind)
    | exact superpose eq149 eq18
    | (have j1 := eq149 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq149
  have eq419 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq189 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq189
    | exact resolve eq189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq448 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq419
    | (have j0 := eq419 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq419 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq1428 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq187 x y
       grind)
    | exact superpose eq187 eq16
    | (have j1 := eq187 x y
       grind)
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq1468 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1428
       have i₂ := eq448 x y
       grind)
    | exact superpose eq448 eq1428
    | (have j1 := eq448 (σ x) (σ y)
       grind)
    | (have r₁ := eq1428
       have r₂ := eq448 x y
       grind)
    | (have r₁ := eq1428
       have r₂ := eq448 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1428
       have r₂ := eq448 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1428 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448 eq1428
  have eq1469 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1468
  have eq1550 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1469
       grind)
    | exact superpose eq1469 eq10
    | exact resolve eq10 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1593 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1550
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1550
    | exact resolve eq1550 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550
  have eq1594 : x = y := by grind
  clear eq1593
  have eq1678 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1594
       grind)
    | exact superpose eq1594 eq16
    | exact resolve eq16 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1679 : False := by grind
  exact eq1679

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then X else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_x_x_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = X0 := by
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
  have eq26 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq26 (σ X0)
       grind)
    | exact superpose eq26 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq53
    | (have j0 := eq53 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq53 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq53 X0 (τ X1)
       grind)
    | exact superpose eq53 eq19
    | (have j1 := eq53 X0 (τ X1)
       grind)
    | exact resolve eq19 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq177 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq253 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq16
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq16 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1500 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq144
    | exact resolve eq144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq1540 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1500 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1500
    | (have j0 := eq1500 X0 X1
       grind)
    | exact resolve eq1500 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500
  have eq1668 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq267 (τ X0) (τ X1)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq267
    | (have j0 := eq267 (τ X0) (τ X1)
       grind)
    | exact resolve eq267 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1684 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1668 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1668
    | (have j0 := eq1668 X0 X1
       grind)
    | exact resolve eq1668 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq1691 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1684 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1684
    | (have j0 := eq1684 X0 X1
       grind)
    | exact resolve eq1684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1693 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1691 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1691
    | (have j0 := eq1691 X0 X1
       grind)
    | exact resolve eq1691 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1694 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1693 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1693
    | (have j0 := eq1693 X0 X1
       grind)
    | exact resolve eq1693 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq1695 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1694 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1694
    | (have j0 := eq1694 X0 X1
       grind)
    | exact resolve eq1694 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694
  have eq1696 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1695 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1695
    | (have j0 := eq1695 X0 X1
       grind)
    | exact resolve eq1695 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq2037 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq139 x y
       grind)
    | exact superpose eq139 eq16
    | (have j1 := eq139 x y
       grind)
    | exact resolve eq16 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq2220 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq253
       have i₂ := eq53 x y
       grind)
    | exact superpose eq53 eq253
    | (have j1 := eq53 x y
       grind)
    | (have r₁ := eq253
       have r₂ := eq53 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq253
       have r₂ := eq53 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq253 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq253
  have eq2223 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq2220
  have eq17931 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq2037
       have i₂ := eq1540 y x
       grind)
    | exact superpose eq1540 eq2037
    | (have j1 := eq1540 y x
       grind)
    | (have r₁ := eq2037
       have r₂ := eq1540 y x
       grind)
    | (have r₁ := eq2037
       have r₂ := eq1540 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2037
       have r₂ := eq1540 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2037 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540 eq2037
  have eq17934 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq17931
  have eq18365 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq2223
       grind)
    | exact superpose eq2223 eq16
    | exact resolve eq16 eq2223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223
  have eq18464 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq18365
       have r₂ := eq17934
       grind)
    | exact resolve eq18365 eq17934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17934 eq18365
  have eq18486 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq267 x y
       have i₂ := eq18464
       grind)
    | exact superpose eq18464 eq267
    | (have j0 := eq267 x y
       grind)
    | exact resolve eq267 eq18464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq18489 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1696 x y
       have i₂ := eq18464
       grind)
    | exact superpose eq18464 eq1696
    | (have j0 := eq1696 x y
       grind)
    | (have r₁ := eq1696 x y
       have r₂ := eq18464
       grind)
    | exact resolve eq1696 eq18464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696 eq18464
  have eq18504 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18489
  have eq18505 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18504
  have eq18508 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18486
  have eq18509 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18508
  have eq19497 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq18509
       grind)
    | exact superpose eq18509 eq16
    | exact resolve eq16 eq18509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18509
  have eq19814 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19497
       have i₂ := eq18505
       grind)
    | exact superpose eq18505 eq19497
    | exact resolve eq19497 eq18505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18505 eq19497
  have eq19815 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19814
  have eq19816 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq19815
  have eq19999 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19816
       grind)
    | exact superpose eq19816 eq10
    | exact resolve eq10 eq19816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19816
  have eq20067 : x = y ∨ x = y := by
    first
    | (have i₁ := eq19999
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19999
    | exact resolve eq19999 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19999
  have eq20068 : x = y := by grind
  clear eq20067
  have eq20208 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20068
       grind)
    | exact superpose eq20068 eq16
    | exact resolve eq16 eq20068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20068
  have eq20209 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20208
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq20208
    | exact resolve eq20208 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20208
  have eq20210 : False := by grind
  exact eq20210

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then X else if X = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_x_y_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = X0 := by
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
  have eq26 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq26 (σ X0)
       grind)
    | exact superpose eq26 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq53
    | (have j0 := eq53 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq53 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq53 X0 (τ X1)
       grind)
    | exact superpose eq53 eq19
    | (have j1 := eq53 X0 (τ X1)
       grind)
    | exact resolve eq19 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq177 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq253 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq16
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq16 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1500 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq144
    | exact resolve eq144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq1540 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1500 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1500
    | (have j0 := eq1500 X0 X1
       grind)
    | exact resolve eq1500 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500
  have eq1668 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq267 (τ X0) (τ X1)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq267
    | (have j0 := eq267 (τ X0) (τ X1)
       grind)
    | exact resolve eq267 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1684 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1668 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1668
    | (have j0 := eq1668 X0 X1
       grind)
    | exact resolve eq1668 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq1691 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1684 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1684
    | (have j0 := eq1684 X0 X1
       grind)
    | exact resolve eq1684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1693 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1691 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1691
    | (have j0 := eq1691 X0 X1
       grind)
    | exact resolve eq1691 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1694 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1693 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1693
    | (have j0 := eq1693 X0 X1
       grind)
    | exact resolve eq1693 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq1695 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1694 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1694
    | (have j0 := eq1694 X0 X1
       grind)
    | exact resolve eq1694 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694
  have eq1696 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1695 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1695
    | (have j0 := eq1695 X0 X1
       grind)
    | exact resolve eq1695 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq2037 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq139 x y
       grind)
    | exact superpose eq139 eq16
    | (have j1 := eq139 x y
       grind)
    | exact resolve eq16 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq2220 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq253
       have i₂ := eq53 x y
       grind)
    | exact superpose eq53 eq253
    | (have j1 := eq53 x y
       grind)
    | (have r₁ := eq253
       have r₂ := eq53 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq253
       have r₂ := eq53 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq253 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq253
  have eq2223 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq2220
  have eq17931 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq2037
       have i₂ := eq1540 y x
       grind)
    | exact superpose eq1540 eq2037
    | (have j1 := eq1540 y x
       grind)
    | (have r₁ := eq2037
       have r₂ := eq1540 y x
       grind)
    | (have r₁ := eq2037
       have r₂ := eq1540 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2037
       have r₂ := eq1540 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2037 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540 eq2037
  have eq17934 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq17931
  have eq18365 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq2223
       grind)
    | exact superpose eq2223 eq16
    | exact resolve eq16 eq2223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223
  have eq18464 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq18365
       have r₂ := eq17934
       grind)
    | exact resolve eq18365 eq17934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17934 eq18365
  have eq18486 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq267 x y
       have i₂ := eq18464
       grind)
    | exact superpose eq18464 eq267
    | (have j0 := eq267 x y
       grind)
    | exact resolve eq267 eq18464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq18489 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1696 x y
       have i₂ := eq18464
       grind)
    | exact superpose eq18464 eq1696
    | (have j0 := eq1696 x y
       grind)
    | (have r₁ := eq1696 x y
       have r₂ := eq18464
       grind)
    | exact resolve eq1696 eq18464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696 eq18464
  have eq18504 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18489
  have eq18505 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18504
  have eq18508 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18486
  have eq18509 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18508
  have eq19497 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq18509
       grind)
    | exact superpose eq18509 eq16
    | exact resolve eq16 eq18509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18509
  have eq19814 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19497
       have i₂ := eq18505
       grind)
    | exact superpose eq18505 eq19497
    | exact resolve eq19497 eq18505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18505 eq19497
  have eq19815 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19814
  have eq19816 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq19815
  have eq19999 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19816
       grind)
    | exact superpose eq19816 eq10
    | exact resolve eq10 eq19816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19816
  have eq20067 : x = y ∨ x = y := by
    first
    | (have i₁ := eq19999
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19999
    | exact resolve eq19999 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19999
  have eq20068 : x = y := by grind
  clear eq20067
  have eq20208 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20068
       grind)
    | exact superpose eq20068 eq16
    | exact resolve eq16 eq20068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20068
  have eq20209 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20208
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq20208
    | exact resolve eq20208 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20208
  have eq20210 : False := by grind
  exact eq20210

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then X else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_x_x_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq26 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq49 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq49
    | (have j0 := eq49 X0 X1 X2
       grind)
    | exact resolve eq49 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq26 (σ X0)
       grind)
    | exact superpose eq26 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq121 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 X0
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 X1 x
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq611 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq121 (σ X0) (σ X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq121
    | (have j0 := eq121 (σ X0) (σ X1)
       have j1 := eq55 X0 X1
       grind)
    | exact resolve eq121 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq636 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq611 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq643 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq636 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq636
    | (have j0 := eq636 X0 X1
       grind)
    | exact resolve eq636 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq644 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq643 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq21515 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 X0
       have i₂ := eq644 X1 X0
       grind)
    | exact superpose eq644 eq55
    | (have j0 := eq55 X1 X0
       have j1 := eq644 X1 X0
       grind)
    | exact resolve eq55 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq644
  have eq21644 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq21515 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21515
  have eq21830 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21644 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21644
    | exact resolve eq21644 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21873 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21644 y x
       grind)
    | exact superpose eq21644 eq16
    | (have j1 := eq21644 x y
       grind)
    | exact resolve eq16 eq21644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21644
  have eq22038 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21830 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq21830
    | (have j0 := eq21830 X0 X1
       grind)
    | exact resolve eq21830 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21830
  have eq22255 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22038 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22038
    | exact resolve eq22038 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22038
  have eq23184 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21873
       have i₂ := eq22255 x y
       grind)
    | exact superpose eq22255 eq21873
    | (have j1 := eq22255 (σ x) (σ y)
       grind)
    | (have r₁ := eq21873
       have r₂ := eq22255 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq21873
       have r₂ := eq22255 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq21873 eq22255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21873 eq22255
  have eq23192 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq23184
  have eq23400 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23192
       grind)
    | exact superpose eq23192 eq10
    | exact resolve eq10 eq23192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23192
  have eq23480 : x = y ∨ x = y := by
    first
    | (have i₁ := eq23400
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23400
    | exact resolve eq23400 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23400
  have eq23481 : x = y := by grind
  clear eq23480
  have eq23682 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23481
       grind)
    | exact superpose eq23481 eq16
    | exact resolve eq16 eq23481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23481
  have eq23683 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq23682
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq23682
    | exact resolve eq23682 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23682
  have eq23684 : False := by grind
  exact eq23684

/-- `Equation4268`: `x ◇ (x ◇ x) = x ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pxy_x_pxy_Equation4268 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4268 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4268.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2
       have i₂ := eq9 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1
       have i₂ := eq9 X1 X1
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
  have eq61 : ∀ X0 X1 X2 : G, X0 = X2 ∨ X0 = X1 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X1 X1
       have j1 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X2)) ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq76 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq74 (M.op X0 X1) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq74 (k X0 X1) (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq74 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq74 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq77 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X2)) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq67 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq67 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq67 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq80 : ∀ X0 X1 X2 : G, X0 = X2 ∨ X0 = X1 ∨ (M.op X1 X2) = (k X1 X2) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq61 X0 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | (have r₁ := eq61 (M.op X0 X0) X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq61 X0 X1 (M.op X0 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq61 (M.op X0 X0) X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq61 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq83 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq80 X0 X1 X2
       have j1 := eq76 X1 X2
       grind)
    | (have r₁ := eq80 X0 X1 X1
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq80 X1 X1 X0
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq80 X0 X1 X2
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq80 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq85 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq76 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq113 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq85 (σ X0)
       grind)
    | exact superpose eq85 eq15
    | exact resolve eq15 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq85 (τ X0)
       grind)
    | exact superpose eq85 eq19
    | exact resolve eq19 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq117
    | exact resolve eq117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq122 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq113
    | exact resolve eq113 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq124 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq118 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq118
    | exact resolve eq118 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq161 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq85 (τ X0)
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq85
    | exact resolve eq85 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq161 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq161
    | exact resolve eq161 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq208 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq77 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq77 eq15
    | (have j1 := eq77 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq15 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) (σ X0) X1
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq24
    | exact resolve eq24 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq221 X0 X1
       have j1 := eq223 X0 X1
       grind)
    | (have r₁ := eq221 X0 X1
       have r₂ := eq223 X0 X1
       grind)
    | (have r₁ := eq221 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have r₂ := eq223 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq221 X0 (σ X0)
       have r₂ := eq223 X0 X1
       grind)
    | exact resolve eq221 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq250 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = X2 ∨ (M.op (σ X0) X2) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq83 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq83 eq15
    | (have j1 := eq83 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq15 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq312 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq313 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq312 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq331 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) X1
       have i₂ := eq164 X0
       grind)
    | exact superpose eq164 eq14
    | (have j0 := eq14 (τ X0) X1
       grind)
    | exact resolve eq14 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq164 X0
       grind)
    | exact superpose eq164 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq331 X0 X1
       have j1 := eq333 X0 X1
       grind)
    | (have r₁ := eq331 X0 X1
       have r₂ := eq333 X0 X1
       grind)
    | (have r₁ := eq331 X0 (τ (M.op (M.op X0 X0) (M.op X0 X0)))
       have r₂ := eq333 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq331 X0 (τ X0)
       have r₂ := eq333 X0 X1
       grind)
    | exact resolve eq331 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq333
  have eq429 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq313 X0 (τ X1)
       grind)
    | exact superpose eq313 eq19
    | (have j1 := eq313 X0 (τ X1)
       grind)
    | exact resolve eq19 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq10
    | (have j1 := eq68 X0 X1
       grind)
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq597 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X1
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq525
    | (have j0 := eq525 X0 X1
       grind)
    | exact resolve eq525 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq663 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq597 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq597
    | (have j0 := eq597 X0 X1
       grind)
    | exact resolve eq597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq717 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq663
    | (have j0 := eq663 X0 X1
       grind)
    | exact resolve eq663 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq3620 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq231 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq231 X0 (σ X0)
       grind)
    | exact superpose eq231 eq10
    | (have j1 := eq231 X1 X0
       grind)
    | exact resolve eq10 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq4065 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq717 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq717
    | (have j0 := eq717 (τ X0) X1
       grind)
    | exact resolve eq717 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4103 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (σ (k X0 X2)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X2 ∨ (M.op (σ X0) (σ X2)) = (k (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq717 X0 X2
       have i₂ := eq77 (σ X2) (σ X0) X1
       grind)
    | exact superpose eq77 eq717
    | (have j0 := eq717 X0 X2
       have j1 := eq77 (σ X2) (σ X0) X2
       grind)
    | exact resolve eq717 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq717
  have eq4293 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (σ (k X0 X2)) ∨ (M.op X0 X0) = X2 ∨ (M.op (σ X0) (σ X2)) = (k (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4103 X0 X1 X2
       have j1 := eq223 X0 (σ X2)
       grind)
    | (have r₁ := eq4103 X0 X1 X2
       have r₂ := eq223 X0 X1
       grind)
    | exact resolve eq4103 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq4103
  have eq4312 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4065 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq4065
    | (have j0 := eq4065 X0 X1
       grind)
    | exact resolve eq4065 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4065
  have eq4368 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (σ (k X0 X2)) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4293 X0 X1 X2
       have i₂ := eq15 X0 X2
       grind)
    | exact superpose eq15 eq4293
    | (have j0 := eq4293 X0 X1 X2
       grind)
    | exact resolve eq4293 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4293
  have eq4380 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4312 X0 X1
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq4312
    | (have j0 := eq4312 X0 X1
       grind)
    | exact resolve eq4312 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq4312
  have eq4416 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4380 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq4380 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq4380 X0 (τ X0)
       have r₂ := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq4380 X0 (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))
       have r₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact resolve eq4380 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4380
  have eq4442 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4416 X0 X1
       have i₂ := eq164 X0
       grind)
    | exact superpose eq164 eq4416
    | (have j0 := eq4416 X0 X1
       grind)
    | exact resolve eq4416 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq4416
  have eq4969 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (M.op (σ X0) X2)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq208 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq5073 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq4442 X0 X1
       grind)
    | exact superpose eq4442 eq23
    | (have j1 := eq4442 X0 X1
       grind)
    | exact resolve eq23 eq4442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq5075 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4442 (σ X0) X1
       grind)
    | exact superpose eq4442 eq15
    | (have j1 := eq4442 (σ X0) X1
       grind)
    | exact resolve eq15 eq4442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4442
  have eq5097 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5075 X0 X1
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq5075
    | (have j0 := eq5075 X0 X1
       grind)
    | exact resolve eq5075 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5075
  have eq5118 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5097 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5097
    | (have j0 := eq5097 X0 X1
       grind)
    | exact resolve eq5097 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5097
  have eq5284 : ∀ X0 X1 X2 : G, (τ X0) = X1 ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (M.op (σ X2) X0) = (k (σ X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1
       have i₂ := eq250 X2 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq250 X0 X1 (σ X0)
       grind)
    | exact superpose eq250 eq10
    | (have j1 := eq250 X2 X1 X0
       grind)
    | exact resolve eq10 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq6443 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5118 x y
       grind)
    | exact superpose eq5118 eq16
    | (have j1 := eq5118 x y
       grind)
    | exact resolve eq16 eq5118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6684 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6443
       have i₂ := eq313 x y
       grind)
    | exact superpose eq313 eq6443
    | (have j1 := eq313 x y
       grind)
    | exact resolve eq6443 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6443
  have eq6690 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq6684
  have eq6691 : y = (M.op x x) := by grind
  clear eq6690
  have eq7376 : ∀ X0 : G, x ≠ y ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq6691
       grind)
    | exact superpose eq6691 eq12
    | (have j0 := eq12 x X0
       grind)
    | exact resolve eq12 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7379 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq228 x X0
       have i₂ := eq6691
       grind)
    | exact superpose eq6691 eq228
    | exact resolve eq228 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq7386 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq24 x X0 x
       have i₂ := eq6691
       grind)
    | exact superpose eq6691 eq24
    | exact resolve eq24 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq12747 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq7379 (σ X0)
       have i₂ := eq5118 x X0
       grind)
    | exact superpose eq5118 eq7379
    | (have j1 := eq5118 x X0
       grind)
    | exact resolve eq7379 eq5118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5118
  have eq12827 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq12747 X0
       have i₂ := eq6691
       grind)
    | exact superpose eq6691 eq12747
    | (have j0 := eq12747 X0
       grind)
    | exact resolve eq12747 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12747
  have eq25125 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq429 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq429
    | exact resolve eq429 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq25511 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25125 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq25125
    | (have j0 := eq25125 X0 X1
       grind)
    | exact resolve eq25125 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25125
  have eq46798 : ∀ X0 X1 X2 : G, (τ X0) = X2 ∨ (σ (k X1 X2)) = (σ (M.op X1 X2)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25511 X2 X1
       have i₂ := eq3620 X0 X1
       grind)
    | exact superpose eq3620 eq25511
    | (have j0 := eq25511 X2 X1
       have j1 := eq3620 X0 X1
       grind)
    | exact resolve eq25511 eq3620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620
  have eq66354 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5073 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5073
    | (have j0 := eq5073 X1 (τ X0)
       grind)
    | exact resolve eq5073 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5073
  have eq66902 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66354 X0 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq66354
    | (have j0 := eq66354 X0 X1
       grind)
    | exact resolve eq66354 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq66354
  have eq86956 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) ≠ (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4969 X1 X0 X2
       have i₂ := eq25511 X0 X1
       grind)
    | exact superpose eq25511 eq4969
    | (have j1 := eq25511 X1 X0
       grind)
    | exact resolve eq4969 eq25511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4969 eq25511
  have eq95254 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (τ X0) = y ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq5284 X0 y x
       grind)
    | exact superpose eq5284 eq16
    | (have j1 := eq5284 X0 y x
       grind)
    | exact resolve eq16 eq5284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5284
  have eq95681 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (τ X0) = y := by
    intro X0
    first
    | (have j0 := eq95254 X0
       have j1 := eq46798 X0 x y
       grind)
    | (have r₁ := eq95254 X0
       have r₂ := eq46798 X0 x y
       grind)
    | exact resolve eq95254 eq46798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46798 eq95254
  have eq96114 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (τ (σ X0)) = y := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq95681 (σ X0)
       grind)
    | exact superpose eq95681 eq15
    | (have j1 := eq95681 (σ X0)
       grind)
    | exact resolve eq15 eq95681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95681
  have eq96231 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq96114 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96114
    | (have j0 := eq96114 X0
       grind)
    | exact resolve eq96114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96114
  have eq96719 : ∀ X0 : G, (τ (σ (k x x))) = X0 ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq341 (σ x) X0
       have i₂ := eq96231 x
       grind)
    | exact superpose eq96231 eq341
    | (have j0 := eq341 (σ x) X0
       have j1 := eq96231 x
       grind)
    | exact resolve eq341 eq96231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq96231
  have eq96830 : ∀ X0 : G, (k x x) = X0 ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq96719 X0
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq96719
    | (have j0 := eq96719 X0
       grind)
    | exact resolve eq96719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96719
  have eq96940 : ∀ X0 : G, (M.op x x) = X0 ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq96830 X0
       have i₂ := eq85 x
       grind)
    | exact superpose eq85 eq96830
    | (have j0 := eq96830 X0
       grind)
    | exact resolve eq96830 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq96830
  have eq96998 : ∀ X0 : G, y = X0 ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq96940 X0
       have i₂ := eq6691
       grind)
    | exact superpose eq6691 eq96940
    | (have j0 := eq96940 X0
       grind)
    | exact resolve eq96940 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96940
  have eq97029 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ y = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq96998 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq96998
    | (have j0 := eq96998 X0
       grind)
    | exact resolve eq96998 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96998
  have eq97045 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq97029 X0
       have j1 := eq7376 X0
       grind)
    | (have r₁ := eq97029 x
       have r₂ := eq7376 X0
       grind)
    | (have r₁ := eq97029 X0
       have r₂ := eq7376 X0
       grind)
    | exact resolve eq97029 eq7376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7376 eq97029
  have eq98195 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq19 X0 x
       have i₂ := eq97045 (τ X0)
       grind)
    | exact superpose eq97045 eq19
    | (have j1 := eq97045 (τ X0)
       grind)
    | exact resolve eq19 eq97045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq97045
  have eq106090 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (M.op x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq98195 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98195
    | exact resolve eq98195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106309 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq106090 X0
       have i₂ := eq15 x X0
       grind)
    | exact superpose eq15 eq106090
    | (have j0 := eq106090 X0
       grind)
    | exact resolve eq106090 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106090
  have eq150122 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq12827 X0
       have i₂ := eq106309 X0
       grind)
    | exact superpose eq106309 eq12827
    | (have j0 := eq12827 X0
       have j1 := eq106309 X0
       grind)
    | exact resolve eq12827 eq106309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12827 eq106309
  have eq150342 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq150122 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150122
  have eq212007 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4368 X0 X1 X1
       have i₂ := eq313 X0 X1
       grind)
    | exact superpose eq313 eq4368
    | (have j0 := eq4368 X0 X1 X1
       have j1 := eq313 X0 X1
       grind)
    | exact resolve eq4368 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq4368
  have eq213126 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq212007 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212007
  have eq213131 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq213126 X0 X1 x
       have j1 := eq86956 X0 X1 x
       grind)
    | (have r₁ := eq213126 X0 X1 x
       have r₂ := eq86956 X0 X1 x
       grind)
    | exact resolve eq213126 eq86956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86956 eq213126
  have eq214515 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq150342 X0
       have i₂ := eq213131 x (M.op x X0)
       grind)
    | exact superpose eq213131 eq150342
    | (have j0 := eq150342 X0
       have j1 := eq213131 x (M.op x X0)
       grind)
    | exact resolve eq150342 eq213131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150342 eq213131
  have eq214809 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = X0 ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq214515 X0
       have i₂ := eq7386 X0
       grind)
    | exact superpose eq7386 eq214515
    | (have j0 := eq214515 X0
       grind)
    | exact resolve eq214515 eq7386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214515
  have eq214882 : ∀ X0 : G, y = X0 ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq214809 X0
       grind)
    | (have r₁ := eq214809 X0
       have r₂ := eq16
       grind)
    | exact resolve eq214809 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214809
  have eq214904 : ∀ X0 : G, y = (M.op x X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq214882 X0
       have i₂ := eq6691
       grind)
    | exact superpose eq6691 eq214882
    | (have j0 := eq214882 (M.op x X0)
       grind)
    | exact resolve eq214882 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214882
  have eq216403 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq7386 X0
       have i₂ := eq214904 (M.op x X0)
       grind)
    | exact superpose eq214904 eq7386
    | (have j1 := eq214904 y
       grind)
    | exact resolve eq7386 eq214904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7386
  have eq216408 : ∀ X0 : G, (σ y) = (k (σ x) X0) ∨ (τ X0) = y ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq98195 X0
       have i₂ := eq214904 (τ X0)
       grind)
    | exact superpose eq214904 eq98195
    | (have j0 := eq98195 X0
       have j1 := eq214904 (τ X0)
       grind)
    | exact resolve eq98195 eq214904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98195 eq214904
  have eq216549 : ∀ X0 : G, (σ y) = (k (σ x) X0) ∨ (τ X0) = y := by
    intro X0
    first
    | (have j0 := eq216408 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216408
  have eq217771 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq216403 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216403
  have eq217772 : y = (M.op x y) := by grind
  clear eq217771
  have eq222525 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (τ (σ y)) ∨ (τ X0) = (τ (M.op (σ x) (σ x))) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq66902 X0 (σ x)
       have i₂ := eq216549 X0
       grind)
    | exact superpose eq216549 eq66902
    | (have j0 := eq66902 X0 (σ x)
       have j1 := eq216549 X0
       grind)
    | exact resolve eq66902 eq216549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66902 eq216549
  have eq222677 : ∀ X0 : G, y = (τ (M.op (σ x) X0)) ∨ (τ X0) = (τ (M.op (σ x) (σ x))) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq222525 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq222525
    | (have j0 := eq222525 X0
       grind)
    | exact resolve eq222525 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222525
  have eq222776 : ∀ X0 : G, (τ X0) = (τ (σ (M.op x x))) ∨ y = (τ (M.op (σ x) X0)) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq222677 X0
       have i₂ := eq122 x
       grind)
    | exact superpose eq122 eq222677
    | (have j0 := eq222677 X0
       grind)
    | exact resolve eq222677 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq222677
  have eq222830 : ∀ X0 : G, (τ X0) = (M.op x x) ∨ y = (τ (M.op (σ x) X0)) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq222776 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq222776
    | (have j0 := eq222776 X0
       grind)
    | exact resolve eq222776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222776
  have eq222852 : ∀ X0 : G, (τ X0) = y ∨ y = (τ (M.op (σ x) X0)) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq222830 X0
       have i₂ := eq6691
       grind)
    | exact superpose eq6691 eq222830
    | (have j0 := eq222830 X0
       grind)
    | exact resolve eq222830 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6691 eq222830
  have eq222853 : ∀ X0 : G, y = (τ (M.op (σ x) X0)) ∨ (τ X0) = y := by
    intro X0
    first
    | (have j0 := eq222852 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222852
  have eq236921 : ∀ X0 : G, y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq222853 (M.op (σ x) X0)
       have i₂ := eq7379 X0
       grind)
    | exact superpose eq7379 eq222853
    | (have j0 := eq222853 (σ y)
       grind)
    | exact resolve eq222853 eq7379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7379 eq222853
  have eq362865 : y ≠ y ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have j0 := eq236921 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236921
  have eq362866 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq362865
  have eq365538 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq362866
       grind)
    | exact superpose eq362866 eq11
    | exact resolve eq11 eq362866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362866
  have eq367671 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq365538
       grind)
    | exact superpose eq365538 eq16
    | exact resolve eq16 eq365538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365538
  have eq367768 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq367671
       have i₂ := eq217772
       grind)
    | exact superpose eq217772 eq367671
    | exact resolve eq367671 eq217772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217772 eq367671
  have eq367769 : False := by grind
  exact eq367769

/-- `Equation4276`: `x ◇ (x ◇ x) = y ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pxy_pxx_pxy_Equation4276 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4276 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4276.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X1)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X0 (M.op X0 X0)) = (k X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq9 X0 X1
       grind)
    | (have i₁ := eq12 X1 (M.op X1 X1)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))
       have r₂ := eq9 (M.op X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       have r₂ := eq9 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq70 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) X1)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq70 (M.op X0 X1) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq70 (k X0 X1) (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq70 (M.op (k X1 X1) X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | exact resolve eq70 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq269 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq37 X0 (M.op X0 (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq320 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X0
       have i₂ := eq14 (σ X0) X1
       grind)
    | (have i₁ := eq62 X0 X1
       have i₂ := eq14 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq14 eq62
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq340 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq9
    | (have j1 := eq62 X0 X0
       grind)
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq371 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq369 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq373 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq340 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq375 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq380 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq320 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq391 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq375 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq375
    | (have j0 := eq375 X0
       grind)
    | exact resolve eq375 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq397 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq380 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq380 (M.op (σ (k X1 X1)) X1) X1
       have r₂ := eq12 (σ (k X1 X1)) X1
       grind)
    | (have r₁ := eq380 (M.op (σ X1) X1) X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | (have r₁ := eq380 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq380 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq413 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq371 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq371
    | (have j0 := eq371 (τ X0)
       grind)
    | exact resolve eq371 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq416 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq413 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq413
    | (have j0 := eq413 X0
       grind)
    | exact resolve eq413 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq419 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq416 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq416
    | (have j0 := eq416 X0
       grind)
    | exact resolve eq416 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq790 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq397 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq397
    | (have j0 := eq397 X1 (τ X0)
       grind)
    | exact resolve eq397 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq868 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq790 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq790
    | (have j0 := eq790 X0 X1
       grind)
    | exact resolve eq790 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq790
  have eq876 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq868 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq868
    | (have j0 := eq868 X0 X1
       grind)
    | exact resolve eq868 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq882 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq876 X0 X1
       have j1 := eq72 X1 X0
       grind)
    | (have r₁ := eq876 X0 X1
       have r₂ := eq72 (k X0 X0) X1
       grind)
    | (have r₁ := eq876 X0 X0
       have r₂ := eq72 X0 (k X0 X0)
       grind)
    | (have r₁ := eq876 X0 X1
       have r₂ := eq72 (M.op X0 X1) (k X0 X1)
       grind)
    | exact resolve eq876 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq876
  have eq910 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq419 X1
       have i₂ := eq882 X1 X0
       grind)
    | (have i₁ := eq419 X0
       have i₂ := eq882 X0 (k X0 X0)
       grind)
    | exact superpose eq882 eq419
    | (have j0 := eq419 X1
       have j1 := eq882 X1 X0
       grind)
    | (have r₁ := eq419 X1
       have r₂ := eq882 X1 X1
       grind)
    | (have r₁ := eq419 (k X0 X0)
       have r₂ := eq882 X0 (k (k X0 X0) (k X0 X0))
       grind)
    | exact resolve eq419 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq930 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ (σ X1))) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1 (σ X1)
       have i₂ := eq882 (σ X1) X0
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq882 X0 (k (σ X0) X1)
       grind)
    | exact superpose eq882 eq33
    | (have j1 := eq882 (σ X1) X0
       grind)
    | exact resolve eq33 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq969 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq930 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq930
    | (have j0 := eq930 X0 X1
       grind)
    | exact resolve eq930 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq1738 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq910 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq1739 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1738 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq1738 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq1738 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738
  have eq1768 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq882 X0 X1
       have i₂ := eq1739 X0
       grind)
    | exact superpose eq1739 eq882
    | (have j0 := eq882 X0 X1
       grind)
    | exact resolve eq882 eq1739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq1777 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1739 (σ X0)
       grind)
    | exact superpose eq1739 eq15
    | exact resolve eq15 eq1739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1796 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1777 X0
       have i₂ := eq1739 X0
       grind)
    | exact superpose eq1739 eq1777
    | exact resolve eq1777 eq1739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq2290 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq1796 X0
       grind)
    | exact superpose eq1796 eq9
    | exact resolve eq9 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5688 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq969 (σ X1) X0
       grind)
    | exact superpose eq969 eq15
    | (have j1 := eq969 (σ X1) X0
       grind)
    | exact resolve eq15 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq5738 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5688 X0 X1
       have i₂ := eq1739 X0
       grind)
    | exact superpose eq1739 eq5688
    | (have j0 := eq5688 X0 X1
       grind)
    | exact resolve eq5688 eq1739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5688
  have eq5841 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5738 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5738
    | (have j0 := eq5738 X0 X1
       grind)
    | exact resolve eq5738 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5738
  have eq9314 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5841 x y
       grind)
    | exact superpose eq5841 eq16
    | (have j1 := eq5841 x y
       grind)
    | exact resolve eq16 eq5841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5841
  have eq10020 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9314
       have i₂ := eq1768 x y
       grind)
    | exact superpose eq1768 eq9314
    | (have j1 := eq1768 x y
       grind)
    | exact resolve eq9314 eq1768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1768 eq9314
  have eq10026 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq10020
  have eq10027 : y = (M.op x x) := by grind
  clear eq10026
  have eq10323 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq10027
       grind)
    | exact superpose eq10027 eq9
    | exact resolve eq9 eq10027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10336 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2290 x X0
       have i₂ := eq10027
       grind)
    | exact superpose eq10027 eq2290
    | exact resolve eq2290 eq10027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10027
  have eq10623 : ∀ X1 : G, (M.op x y) = (M.op (σ X1) (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq2290 X1 x
       have i₂ := eq10323 x
       grind)
    | exact superpose eq10323 eq2290
    | exact resolve eq2290 eq10323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq10848 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq373 X0 X1
       have i₂ := eq391 X0
       grind)
    | exact superpose eq391 eq373
    | (have j0 := eq373 X0 X1
       have j1 := eq391 X0
       grind)
    | exact resolve eq373 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq391
  have eq10864 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq10848 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10848
  have eq10881 : ∀ X0 : G, (σ X0) = (M.op x y) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10864 X0 x
       have i₂ := eq10323 x
       grind)
    | exact superpose eq10323 eq10864
    | (have j0 := eq10864 X0 x
       grind)
    | exact resolve eq10864 eq10323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10864
  have eq10941 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op x y) ∨ (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10881 X0
       have i₂ := eq1796 X0
       grind)
    | exact superpose eq1796 eq10881
    | (have j0 := eq10881 X0
       grind)
    | exact resolve eq10881 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10881
  have eq10997 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10941 X0
       have i₂ := eq1739 X0
       grind)
    | exact superpose eq1739 eq10941
    | (have j0 := eq10941 X0
       grind)
    | exact resolve eq10941 eq1739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739 eq10941
  have eq13722 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq10336 X0
       grind)
    | exact superpose eq10336 eq16
    | exact resolve eq16 eq10336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10336
  have eq13745 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq13722 x
       have i₂ := eq10323 x
       grind)
    | exact superpose eq10323 eq13722
    | exact resolve eq13722 eq10323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13722
  have eq171733 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) ∨ (σ (M.op X0 (M.op X0 X0))) = (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) ∨ (M.op x y) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10997 (M.op X0 (M.op X0 X0))
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq10997
    | (have j0 := eq10997 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq10997 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq10997
  have eq172033 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) ∨ (M.op x y) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq171733 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171733
  have eq172043 : ∀ X0 : G, (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq172033 X0
       have i₂ := eq10323 X0
       grind)
    | exact superpose eq10323 eq172033
    | (have j0 := eq172033 X0
       grind)
    | exact resolve eq172033 eq10323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172033
  have eq172046 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq172043 x
       have i₂ := eq10323 x
       grind)
    | exact superpose eq10323 eq172043
    | exact resolve eq172043 eq10323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10323 eq172043
  have eq172049 : (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have r₁ := eq172046
       have r₂ := eq13745
       grind)
    | exact resolve eq172046 eq13745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172046
  have eq172084 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10623 (M.op x y)
       have i₂ := eq172049
       grind)
    | exact superpose eq172049 eq10623
    | exact resolve eq10623 eq172049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10623
  have eq172089 : (M.op (M.op x y) (M.op x y)) = (τ (σ (M.op x y))) := by
    first
    | (have i₁ := eq10 (M.op (M.op x y) (M.op x y))
       have i₂ := eq172049
       grind)
    | exact superpose eq172049 eq10
    | exact resolve eq10 eq172049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172049
  have eq172133 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq172089
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq172089
    | exact resolve eq172089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172089
  have eq172137 : (M.op x y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq172084
       have i₂ := eq1796 (M.op x y)
       grind)
    | exact superpose eq1796 eq172084
    | exact resolve eq172084 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796 eq172084
  have eq172160 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq172137
       have i₂ := eq172133
       grind)
    | exact superpose eq172133 eq172137
    | exact resolve eq172137 eq172133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172133 eq172137
  have eq172178 : False := by grind
  exact eq172178

/-- `Equation4279`: `x ◇ (x ◇ x) = y ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyx_y_pyx_Equation4279 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4279 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4279.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X4 X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq9 x X3 X4
       have i₂ := eq9 x X0 X1
       grind)
    | (have i₁ := eq9 x X1 x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X2 X3) X3
       have i₂ := eq9 X0 X3 X2
       grind)
    | (have i₁ := eq9 X0 (M.op X0 X0) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq71 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq73 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op (M.op X1 X1) X0) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq77 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq73 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq73 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq73 (M.op (k X1 X1) X0) X1
       have r₂ := eq12 X0 (k X1 X1)
       grind)
    | exact resolve eq73 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq79 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq75 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq75 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq127 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq79 (τ X1) X0
       grind)
    | exact superpose eq79 eq18
    | (have j1 := eq79 (τ X1) X0
       grind)
    | exact resolve eq18 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq129 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq233 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (k (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) ∨ (M.op X1 (M.op X1 X1)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    grind
  clear eq27
  have eq242 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (k (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq233 X0 X1
       have j1 := eq129 (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       grind)
    | (have r₁ := eq233 X0 X1
       have r₂ := eq129 (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       grind)
    | exact resolve eq233 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq839 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X0
       have i₂ := eq14 X0 (σ X0)
       grind)
    | (have i₁ := eq68 X0 X1
       have i₂ := eq14 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq14 eq68
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq68 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq922 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq924 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq922 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq937 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq839 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq957 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq937 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq937 (M.op (σ (k X1 X1)) X0) X1
       have r₂ := eq12 X0 (σ (k X1 X1))
       grind)
    | (have r₁ := eq937 (M.op (σ X1) X0) X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq937 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq937 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq1310 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq924 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq924
    | (have j0 := eq924 (τ X0)
       grind)
    | exact resolve eq924 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq1313 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1310 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1310
    | (have j0 := eq1310 X0
       grind)
    | exact resolve eq1310 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq1316 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1313 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1313
    | (have j0 := eq1313 X0
       grind)
    | exact resolve eq1313 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1320 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq127
    | exact resolve eq127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq1352 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1320 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1320
    | (have j0 := eq1320 X0 X1
       grind)
    | exact resolve eq1320 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq7149 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq957 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq957
    | (have j0 := eq957 X1 (τ X0)
       grind)
    | exact resolve eq957 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq7285 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7149 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq7149
    | (have j0 := eq7149 X0 X1
       grind)
    | exact resolve eq7149 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq7149
  have eq7293 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7285 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7285
    | (have j0 := eq7285 X0 X1
       grind)
    | exact resolve eq7285 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7285
  have eq7299 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq7293 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq7293 X0 X1
       have r₂ := eq77 (k X0 X0) X1
       grind)
    | (have r₁ := eq7293 X0 X0
       have r₂ := eq77 X0 (k X0 X0)
       grind)
    | (have r₁ := eq7293 X0 X1
       have r₂ := eq77 (M.op X0 X1) (k X1 X0)
       grind)
    | exact resolve eq7293 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq7293
  have eq7344 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1316 X1
       have i₂ := eq7299 X1 X0
       grind)
    | (have i₁ := eq1316 X0
       have i₂ := eq7299 X0 (k X0 X0)
       grind)
    | exact superpose eq7299 eq1316
    | (have j0 := eq1316 X1
       have j1 := eq7299 X1 X0
       grind)
    | (have r₁ := eq1316 X1
       have r₂ := eq7299 X1 X1
       grind)
    | (have r₁ := eq1316 (k X0 X0)
       have r₂ := eq7299 X0 (k (k X0 X0) (k X0 X0))
       grind)
    | exact resolve eq1316 eq7299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq13098 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7344 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7344
  have eq13099 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13098 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq13098 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq13098 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13098
  have eq13209 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq13099 (σ X0)
       grind)
    | exact superpose eq13099 eq15
    | exact resolve eq15 eq13099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13215 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0 X0
       have i₂ := eq13099 (τ X0)
       grind)
    | exact superpose eq13099 eq40
    | exact resolve eq40 eq13099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13222 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13215 X0
       have i₂ := eq13099 X0
       grind)
    | exact superpose eq13099 eq13215
    | exact resolve eq13215 eq13099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13215
  have eq13228 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13209 X0
       have i₂ := eq13099 X0
       grind)
    | exact superpose eq13099 eq13209
    | exact resolve eq13209 eq13099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13209
  have eq14130 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  have eq14260 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq14130 X0
       have j1 := eq129 (τ (M.op X0 X0)) (τ X0)
       grind)
    | (have r₁ := eq14130 X0
       have r₂ := eq129 (τ (M.op X0 X0)) (τ X0)
       grind)
    | exact resolve eq14130 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq14130
  have eq14281 : ∀ X0 : G, (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14260 X0
       have i₂ := eq40 X0 (M.op X0 X0)
       grind)
    | exact superpose eq40 eq14260
    | exact resolve eq14260 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14260
  have eq15072 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14281 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq14281 X0
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq14281
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq14281 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15125 : ∀ X0 : G, (σ (τ X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11 (k (M.op X0 X0) X0)
       have i₂ := eq14281 X0
       grind)
    | exact superpose eq14281 eq11
    | exact resolve eq11 eq14281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15128 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 (k (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (k (M.op X0 X0) X0) X1
       have i₂ := eq14281 X0
       grind)
    | exact superpose eq14281 eq40
    | exact resolve eq40 eq14281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15129 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k (k (M.op X0 X0) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 (k (M.op X0 X0) X0)
       have i₂ := eq14281 X0
       grind)
    | exact superpose eq14281 eq40
    | exact resolve eq40 eq14281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14281
  have eq15139 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (k (k (M.op X0 X0) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15129 X0 X1
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq15129
    | exact resolve eq15129 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15129
  have eq15140 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (k X1 (k (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15128 X0 X1
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq15128
    | exact resolve eq15128 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15128
  have eq15143 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15125 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15125
    | exact resolve eq15125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15125
  have eq15157 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq15072 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq15072 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq15072 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15072
  have eq16872 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 (σ X0) (σ X0)
       have i₂ := eq13228 X0
       grind)
    | exact superpose eq13228 eq24
    | exact resolve eq24 eq13228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18988 : ∀ X0 X3 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ X3) (σ (M.op X3 X3))) := by
    intro X0 X3
    first
    | (have i₁ := eq16872 X3 x x
       have i₂ := eq16872 X0 x x
       grind)
    | exact superpose eq16872 eq16872
    | exact resolve eq16872 eq16872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20148 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 (k (M.op X1 X1) X1))) ∨ (k X0 (k (M.op X1 X1) X1)) = (M.op (k (M.op X1 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15139 X1 (k (M.op X1 X1) X1)
       have i₂ := eq7299 (k (M.op X1 X1) X1) X0
       grind)
    | (have i₁ := eq15139 X0 X1
       have i₂ := eq7299 X0 (k (k (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq7299 eq15139
    | (have j1 := eq7299 (k (M.op X1 X1) X1) X0
       grind)
    | exact resolve eq15139 eq7299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7299 eq15139
  have eq20210 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X1)) ∨ (k X0 (k (M.op X1 X1) X1)) = (M.op (k (M.op X1 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20148 X0 X1
       have i₂ := eq15140 X1 X1
       grind)
    | exact superpose eq15140 eq20148
    | (have j0 := eq20148 X0 X1
       grind)
    | exact resolve eq20148 eq15140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15140 eq20148
  have eq20250 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X1 X1)) ∨ (k X0 (k (M.op X1 X1) X1)) = (M.op (k (M.op X1 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20210 X0 X1
       have i₂ := eq13099 X1
       grind)
    | exact superpose eq13099 eq20210
    | (have j0 := eq20210 X0 X1
       grind)
    | exact resolve eq20210 eq13099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20210
  have eq20286 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20250 X0 X0
       have i₂ := eq15143 X0
       grind)
    | exact superpose eq15143 eq20250
    | (have j0 := eq20250 X0 X1
       grind)
    | exact resolve eq20250 eq15143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15143 eq20250
  have eq23854 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15157 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq15157
    | exact resolve eq15157 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15157
  have eq23921 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23854 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq23854
    | (have j0 := eq23854 X0 X1
       grind)
    | exact resolve eq23854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23854
  have eq23931 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23921 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq23921
    | (have j0 := eq23921 X0 X1
       grind)
    | exact resolve eq23921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23921
  have eq25998 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (M.op (σ X0) (σ X0))) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq20286 (σ X1) (σ X0)
       grind)
    | exact superpose eq20286 eq15
    | (have j1 := eq20286 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq20286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20286
  have eq26125 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25998 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq25998
    | (have j0 := eq25998 X0 X1
       grind)
    | exact resolve eq25998 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25998
  have eq26182 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26125 X0 X1
       have i₂ := eq13228 X0
       grind)
    | exact superpose eq13228 eq26125
    | (have j0 := eq26125 X0 X1
       grind)
    | exact resolve eq26125 eq13228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26125
  have eq26209 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26182 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq26182
    | (have j0 := eq26182 X0 X1
       grind)
    | exact resolve eq26182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26182
  have eq35587 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq923 (τ X1) (τ X0)
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq923
    | (have j0 := eq923 (τ X1) (τ X0)
       grind)
    | exact resolve eq923 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq923
  have eq35660 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35587 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq35587
    | (have j0 := eq35587 X0 X1
       grind)
    | exact resolve eq35587 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35587
  have eq35708 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35660 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq35660
    | (have j0 := eq35660 X0 X1
       grind)
    | exact resolve eq35660 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35660
  have eq35722 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35708 X0 X1
       have i₂ := eq13228 (τ X1)
       grind)
    | exact superpose eq13228 eq35708
    | (have j0 := eq35708 X0 X1
       grind)
    | exact resolve eq35708 eq13228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35708
  have eq35732 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35722 X0 X1
       have i₂ := eq13222 X1
       grind)
    | exact superpose eq13222 eq35722
    | (have j0 := eq35722 X0 X1
       grind)
    | exact resolve eq35722 eq13222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13222 eq35722
  have eq35738 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35732 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq35732
    | (have j0 := eq35732 X0 X1
       grind)
    | exact resolve eq35732 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35732
  have eq35742 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35738 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35738
    | (have j0 := eq35738 X0 X1
       grind)
    | exact resolve eq35738 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35738
  have eq35746 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35742 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35742
    | (have j0 := eq35742 X0 X1
       grind)
    | exact resolve eq35742 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35742
  have eq35747 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35746 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35746
    | (have j0 := eq35746 X0 X1
       grind)
    | exact resolve eq35746 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35746
  have eq64453 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23931 y x
       grind)
    | exact superpose eq23931 eq16
    | (have j1 := eq23931 y x
       grind)
    | exact resolve eq16 eq23931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23931
  have eq64787 : x = (k y x) := by
    first
    | (have j1 := eq1352 y x
       grind)
    | (have r₁ := eq64453
       have r₂ := eq1352 y x
       grind)
    | exact resolve eq64453 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352 eq64453
  have eq66651 : x ≠ x ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35747 y x
       have i₂ := eq64787
       grind)
    | exact superpose eq64787 eq35747
    | (have j0 := eq35747 y x
       grind)
    | (have r₁ := eq35747 y x
       have r₂ := eq64787
       grind)
    | exact resolve eq35747 eq64787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35747
  have eq66652 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq66651
  have eq81195 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26209 x y
       grind)
    | exact superpose eq26209 eq16
    | (have j1 := eq26209 x y
       grind)
    | exact resolve eq16 eq26209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26209
  have eq81561 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq81195
       have i₂ := eq64787
       grind)
    | exact superpose eq64787 eq81195
    | exact resolve eq81195 eq64787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64787 eq81195
  have eq82491 : (σ x) ≠ (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq81561
       have i₂ := eq66652
       grind)
    | exact superpose eq66652 eq81561
    | exact resolve eq81561 eq66652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66652 eq81561
  have eq82495 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by grind
  clear eq82491
  have eq82496 : y = (M.op x x) := by grind
  clear eq82495
  have eq83064 : ∀ X0 : G, (M.op x y) = (k (M.op X0 (M.op X0 X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq242 X0 x
       have i₂ := eq82496
       grind)
    | exact superpose eq82496 eq242
    | exact resolve eq242 eq82496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq83115 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16872 x X0 X1
       have i₂ := eq82496
       grind)
    | exact superpose eq82496 eq16872
    | exact resolve eq16872 eq82496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83130 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1 x x
       have i₂ := eq82496
       grind)
    | exact superpose eq82496 eq24
    | exact resolve eq24 eq82496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq82496
  have eq83229 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83115 x x
       have i₂ := eq83130 x x
       grind)
    | exact superpose eq83130 eq83115
    | exact resolve eq83115 eq83130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83115
  have eq83244 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq83064 x
       have i₂ := eq83130 x x
       grind)
    | exact superpose eq83130 eq83064
    | exact resolve eq83064 eq83130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83064
  have eq83281 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq83244
       have i₂ := eq13099 (M.op x y)
       grind)
    | exact superpose eq13099 eq83244
    | exact resolve eq83244 eq13099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13099 eq83244
  have eq84402 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq83130 (M.op X0 X1) X1
       have i₂ := eq83130 X1 X0
       grind)
    | exact superpose eq83130 eq83130
    | exact resolve eq83130 eq83130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84733 : ∀ X2 : G, (M.op x y) = (M.op (σ X2) (σ (M.op X2 X2))) := by
    intro X2
    first
    | (have i₁ := eq16872 X2 x x
       have i₂ := eq83130 x x
       grind)
    | exact superpose eq83130 eq16872
    | exact resolve eq16872 eq83130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16872 eq83130
  have eq85932 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83229
       grind)
    | exact superpose eq83229 eq16
    | exact resolve eq16 eq83229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83229
  have eq94631 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq18988 X0 (M.op x y)
       have i₂ := eq83281
       grind)
    | exact superpose eq83281 eq18988
    | exact resolve eq18988 eq83281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18988 eq83281
  have eq94802 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq94631 X0
       have i₂ := eq13228 (M.op x y)
       grind)
    | exact superpose eq13228 eq94631
    | exact resolve eq94631 eq13228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13228 eq94631
  have eq94874 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq94802 X0
       have i₂ := eq84402 x y
       grind)
    | exact superpose eq84402 eq94802
    | exact resolve eq94802 eq84402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84402 eq94802
  have eq94906 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq94874 x
       have i₂ := eq84733 x
       grind)
    | exact superpose eq84733 eq94874
    | exact resolve eq94874 eq84733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84733 eq94874
  have eq94922 : False := by grind
  exact eq94922
