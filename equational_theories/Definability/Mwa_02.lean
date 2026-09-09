import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation614`: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_pxx_pxy_Equation614 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law614 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law614.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = M.op a a :=
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq89 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq89 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq89 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq171 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq15
    | (have j1 := eq92 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq92 (τ X0) X1
       grind)
    | exact superpose eq92 eq18
    | (have j1 := eq92 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq92
  have eq583 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq173 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq173
    | exact resolve eq173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq621 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq583 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq583
    | (have j0 := eq583 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq583 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq1749 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq171 x y
       grind)
    | exact superpose eq171 eq16
    | (have j1 := eq171 x y
       grind)
    | exact resolve eq16 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq1954 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1749
       have i₂ := eq621 x y
       grind)
    | exact superpose eq621 eq1749
    | (have j1 := eq621 (σ x) (σ y)
       grind)
    | (have r₁ := eq1749
       have r₂ := eq621 x y
       grind)
    | (have r₁ := eq1749
       have r₂ := eq621 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1749
       have r₂ := eq621 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1749 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq1749
  have eq1955 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1954
  have eq1974 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1955
       grind)
    | exact superpose eq1955 eq10
    | exact resolve eq10 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955
  have eq2020 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1974
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1974
    | exact resolve eq1974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974
  have eq2021 : x = y := by grind
  clear eq2020
  have eq2086 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2021
       grind)
    | exact superpose eq2021 eq16
    | exact resolve eq16 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021
  have eq2087 : False := by grind
  exact eq2087

/-- `Equation614`: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation614 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law614 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law614.models_iff G M).mp hM
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq89 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq89 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq89 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq171 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq15
    | (have j1 := eq92 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq92 (τ X0) X1
       grind)
    | exact superpose eq92 eq18
    | (have j1 := eq92 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq92
  have eq583 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq173 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq173
    | exact resolve eq173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq621 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq583 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq583
    | (have j0 := eq583 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq583 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq1749 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq171 x y
       grind)
    | exact superpose eq171 eq16
    | (have j1 := eq171 x y
       grind)
    | exact resolve eq16 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq1954 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1749
       have i₂ := eq621 x y
       grind)
    | exact superpose eq621 eq1749
    | (have j1 := eq621 (σ x) (σ y)
       grind)
    | (have r₁ := eq1749
       have r₂ := eq621 x y
       grind)
    | (have r₁ := eq1749
       have r₂ := eq621 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1749
       have r₂ := eq621 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1749 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq1749
  have eq1955 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1954
  have eq1974 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1955
       grind)
    | exact superpose eq1955 eq10
    | exact resolve eq10 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955
  have eq2020 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1974
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1974
    | exact resolve eq1974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974
  have eq2021 : x = y := by grind
  clear eq2020
  have eq2086 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2021
       grind)
    | exact superpose eq2021 eq16
    | exact resolve eq16 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021
  have eq2087 : False := by grind
  exact eq2087

/-- `Equation614`: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_x_pyx_Equation614 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law614 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law614.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq54 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq59 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq54 (σ X1) (σ X0)
       grind)
    | exact superpose eq54 eq15
    | (have j1 := eq54 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq54 (τ X1) X0
       grind)
    | exact superpose eq54 eq18
    | (have j1 := eq54 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq54
  have eq168 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60
    | exact resolve eq60 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq168 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq168
    | (have j0 := eq168 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq168 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq571 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq16
    | (have j1 := eq59 x y
       grind)
    | exact resolve eq16 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq591 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq571
       have i₂ := eq190 y x
       grind)
    | exact superpose eq190 eq571
    | (have j1 := eq190 (σ x) (σ y)
       grind)
    | (have r₁ := eq571
       have r₂ := eq190 y x
       grind)
    | (have r₁ := eq571
       have r₂ := eq190 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq571
       have r₂ := eq190 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq571 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq571
  have eq592 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq591
  have eq673 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq592
       grind)
    | exact superpose eq592 eq10
    | exact resolve eq10 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq708 : x = y ∨ x = y := by
    first
    | (have i₁ := eq673
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq673
    | exact resolve eq673 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq709 : x = y := by grind
  clear eq708
  have eq798 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq709
       grind)
    | exact superpose eq709 eq16
    | exact resolve eq16 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq799 : False := by grind
  exact eq799

/-- `Equation614`: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_x_pyx_Equation614 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law614 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law614.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq52
    | (have j0 := eq52 (σ (k X0 X1)) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq52 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq91 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq88 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq88 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq73
    | (have j0 := eq73 X0 X1
       grind)
    | exact resolve eq73 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq212 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq221 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq212 X0 X1
       have j1 := eq96 X1 X0
       grind)
    | (have r₁ := eq212 X1 X0
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq212 X0 X1
       have r₂ := eq96 (k X1 X0) (M.op X1 X1)
       grind)
    | (have r₁ := eq212 X0 X1
       have r₂ := eq96 (M.op X1 X1) (k X1 X0)
       grind)
    | exact resolve eq212 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq212
  have eq249 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq91 (τ X1) X0
       grind)
    | exact superpose eq91 eq18
    | (have j1 := eq91 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq91
  have eq637 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq249 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq249
    | exact resolve eq249 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq674 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq637 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq637
    | (have j0 := eq637 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq637 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq691 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq221 x y
       grind)
    | exact superpose eq221 eq16
    | (have j1 := eq221 x y
       grind)
    | exact resolve eq16 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq1092 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq691
       have i₂ := eq674 y x
       grind)
    | exact superpose eq674 eq691
    | (have j1 := eq674 (σ x) (σ y)
       grind)
    | (have r₁ := eq691
       have r₂ := eq674 y x
       grind)
    | (have r₁ := eq691
       have r₂ := eq674 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq691
       have r₂ := eq674 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq691 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq691
  have eq1093 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1092
  have eq1175 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1093
       grind)
    | exact superpose eq1093 eq10
    | exact resolve eq10 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1211 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1175
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1175
    | exact resolve eq1175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1212 : x = y := by grind
  clear eq1211
  have eq1326 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1212
       grind)
    | exact superpose eq1212 eq16
    | exact resolve eq16 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1327 : False := by grind
  exact eq1327

/-- `Equation614`: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_Equation614 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law614 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law614.models_iff G M).mp hM
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq53 (σ X0) (σ X1)
       grind)
    | exact superpose eq53 eq15
    | (have j1 := eq53 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq53 (τ X0) X1
       grind)
    | exact superpose eq53 eq18
    | (have j1 := eq53 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq53
  have eq184 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59
    | exact resolve eq59 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq208 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq184
    | (have j0 := eq184 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq184 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq566 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq16
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq16 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq662 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq566
       have i₂ := eq208 x y
       grind)
    | exact superpose eq208 eq566
    | (have j1 := eq208 (σ x) (σ y)
       grind)
    | (have r₁ := eq566
       have r₂ := eq208 x y
       grind)
    | (have r₁ := eq566
       have r₂ := eq208 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq566
       have r₂ := eq208 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq566 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq566
  have eq663 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq662
  have eq758 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq663
       grind)
    | exact superpose eq663 eq10
    | exact resolve eq10 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq793 : x = y ∨ x = y := by
    first
    | (have i₁ := eq758
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq758
    | exact resolve eq758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq794 : x = y := by grind
  clear eq793
  have eq965 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq794
       grind)
    | exact superpose eq794 eq16
    | exact resolve eq16 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq966 : False := by grind
  exact eq966

/-- `Equation614`: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation614 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law614 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law614.models_iff G M).mp hM
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
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
  have eq59 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq46 X1 X1 X2
       have j1 := eq54 X1 X1 X2
       grind)
    | (have r₁ := eq46 X0 X1 X2
       have r₂ := eq54 X0 X1 X2
       grind)
    | (have r₁ := eq46 X1 X0 X2
       have r₂ := eq54 X0 X1 X2
       grind)
    | (have r₁ := eq46 X0 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq54 X0 X1 X2
       grind)
    | exact resolve eq46 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq54
  have eq126 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq127 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq126 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq128 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq183 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq128 (σ X0) (σ X1)
       grind)
    | exact superpose eq128 eq15
    | (have j1 := eq128 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq128 (τ X0) X1
       grind)
    | exact superpose eq128 eq18
    | (have j1 := eq128 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq128
  have eq322 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
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
  have eq345 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq322 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq322
    | (have j0 := eq322 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq322 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq1461 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
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
  have eq1551 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1461
       have i₂ := eq345 x y
       grind)
    | exact superpose eq345 eq1461
    | (have j1 := eq345 (σ x) (σ y)
       grind)
    | (have r₁ := eq1461
       have r₂ := eq345 x y
       grind)
    | (have r₁ := eq1461
       have r₂ := eq345 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1461
       have r₂ := eq345 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1461 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq1461
  have eq1552 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1551
  have eq1632 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1552
       grind)
    | exact superpose eq1552 eq10
    | exact resolve eq10 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq1673 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1632
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1632
    | exact resolve eq1632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq1674 : x = y := by grind
  clear eq1673
  have eq1748 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1674
       grind)
    | exact superpose eq1674 eq16
    | exact resolve eq16 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq1749 : False := by grind
  exact eq1749

/-- `Equation614`: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pyx_Equation614 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law614 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law614.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq48 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X0
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
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq14 X1 X0
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
  have eq57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq59 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq113 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq148 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq270 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq59 X0 X1
       grind)
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq10
    | (have j1 := eq59 X0 X1
       grind)
    | exact resolve eq10 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq285 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq270
    | (have j0 := eq270 X0 X1
       grind)
    | exact resolve eq270 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq1159 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq1303 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq285 x y
       grind)
    | exact superpose eq285 eq16
    | (have j1 := eq285 x y
       grind)
    | exact resolve eq16 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq1492 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1656 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1492 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1492
    | (have j0 := eq1492 X0 X1
       grind)
    | exact resolve eq1492 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq2058 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X1 (σ X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq113
    | (have j0 := eq113 X1 (σ X0)
       grind)
    | (have r₁ := eq113 X0 (σ X0)
       have r₂ := eq39 X0
       grind)
    | exact resolve eq113 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq2087 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2058 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2058
    | (have j0 := eq2058 X0 X1
       grind)
    | exact resolve eq2058 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058
  have eq27422 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1303
       have i₂ := eq1656 y x
       grind)
    | exact superpose eq1656 eq1303
    | (have j1 := eq1656 x y
       grind)
    | (have r₁ := eq1303
       have r₂ := eq1656 y x
       grind)
    | (have r₁ := eq1303
       have r₂ := eq1656 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1303
       have r₂ := eq1656 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1303 eq1656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303 eq1656
  have eq27423 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27422
  have eq27424 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27423
  have eq28416 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq27424
       grind)
    | exact superpose eq27424 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq27424
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq27424
       grind)
    | exact resolve eq12 eq27424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28522 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2087 y X0
       have i₂ := eq27424
       grind)
    | exact superpose eq27424 eq2087
    | (have j0 := eq2087 X0 x
       grind)
    | exact resolve eq2087 eq27424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087 eq27424
  have eq61936 : (k y x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq28416 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28416
  have eq62114 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq125 x y
       have i₂ := eq61936
       grind)
    | exact superpose eq61936 eq125
    | (have j0 := eq125 x y
       grind)
    | exact resolve eq125 eq61936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq61936
  have eq62147 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq62114
  have eq62177 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq1159 x y
       grind)
    | (have r₁ := eq62147
       have r₂ := eq1159 x y
       grind)
    | (have r₁ := eq62147
       have r₂ := eq1159 y x
       grind)
    | exact resolve eq62147 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159 eq62147
  have eq132415 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq28522 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28522
  have eq132429 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq132415
       grind)
    | exact superpose eq132415 eq16
    | exact resolve eq16 eq132415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132415
  have eq132495 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq132429
       have i₂ := eq62177
       grind)
    | exact superpose eq62177 eq132429
    | exact resolve eq132429 eq62177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62177 eq132429
  have eq132514 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq132495
  have eq132515 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq132514
  have eq132517 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq132515
       grind)
    | exact superpose eq132515 eq10
    | exact resolve eq10 eq132515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132515
  have eq132927 : x = y ∨ x = y := by
    first
    | (have i₁ := eq132517
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq132517
    | exact resolve eq132517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132517
  have eq132928 : x = y := by grind
  clear eq132927
  have eq132930 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq132928
       grind)
    | exact superpose eq132928 eq16
    | exact resolve eq16 eq132928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132928
  have eq132931 : False := by grind
  exact eq132931

/-- `Equation614`: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation614 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law614 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law614.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq84 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq16
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq358 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (τ X1) (τ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq90
    | (have j0 := eq90 (τ X1) (τ X0)
       grind)
    | exact resolve eq90 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq358 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq358
    | (have j0 := eq358 X0 X1
       grind)
    | exact resolve eq358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq368 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq365
    | (have j0 := eq365 X0 X1
       grind)
    | exact resolve eq365 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq370 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq371 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq370 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq370
    | (have j0 := eq370 X0 X1
       grind)
    | exact resolve eq370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq372 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq371 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq371
    | (have j0 := eq371 X0 X1
       grind)
    | exact resolve eq371 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq373 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq372
    | (have j0 := eq372 X0 X1
       grind)
    | exact resolve eq372 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq423 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X1) (τ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq91
    | (have j0 := eq91 (τ X1) (τ X0)
       grind)
    | exact resolve eq91 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq431 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq423 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq423
    | (have j0 := eq423 X0 X1
       grind)
    | exact resolve eq423 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq434 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq431 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq431
    | (have j0 := eq431 X0 X1
       grind)
    | exact resolve eq431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq436 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq434 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq434
    | (have j0 := eq434 X0 X1
       grind)
    | exact resolve eq434 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq437 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq436 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq436
    | (have j0 := eq436 X0 X1
       grind)
    | exact resolve eq436 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq438 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
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
  have eq439 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq438 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq438
    | (have j0 := eq438 X0 X1
       grind)
    | exact resolve eq438 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq485 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq84
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq84 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq485
  have eq3351 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq486
       grind)
    | exact superpose eq486 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq486
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq486
       grind)
    | exact resolve eq12 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq3353 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3351
  have eq3354 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3353
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3353
    | exact resolve eq3353 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353
  have eq20916 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3354
       grind)
    | exact superpose eq3354 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3354
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3354
       grind)
    | exact resolve eq13 eq3354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20917 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3354
       grind)
    | exact superpose eq3354 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3354
       grind)
    | exact resolve eq12 eq3354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3354
  have eq20918 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20916
  have eq20921 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20917
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq20917
    | exact resolve eq20917 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20917
  have eq20922 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20921
  have eq20923 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20918
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq20918
    | exact resolve eq20918 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20918
  have eq20925 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20923
       have r₂ := eq20922
       grind)
    | exact resolve eq20923 eq20922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20922 eq20923
  have eq21638 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq20925
       grind)
    | exact superpose eq20925 eq10
    | exact resolve eq10 eq20925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20925
  have eq21790 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21638
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq21638
    | exact resolve eq21638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21638
  have eq21793 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq439 y x
       grind)
    | (have r₁ := eq21790
       have r₂ := eq439 y x
       grind)
    | exact resolve eq21790 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq21790
  have eq22049 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq21793
       grind)
    | exact superpose eq21793 eq10
    | exact resolve eq10 eq21793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21793
  have eq22201 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22049
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22049
    | exact resolve eq22049 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22049
  have eq22202 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq373 y x
       grind)
    | (have r₁ := eq22201
       have r₂ := eq373 y x
       grind)
    | exact resolve eq22201 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq22201
  have eq22721 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq22202
       grind)
    | exact resolve eq12 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22722 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq22723 : x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq22721
  have eq23228 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90 x y
       have i₂ := eq22723
       grind)
    | exact superpose eq22723 eq90
    | (have j0 := eq90 x y
       grind)
    | exact resolve eq90 eq22723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq23273 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23228
  have eq29039 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23273
       grind)
    | exact superpose eq23273 eq16
    | exact resolve eq16 eq23273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23273
  have eq29703 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29039
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq29039
    | exact resolve eq29039 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29039
  have eq29706 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq29703
  have eq29707 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq29706
       have r₂ := eq22722
       grind)
    | exact resolve eq29706 eq22722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29706
  have eq30058 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29707
       grind)
    | exact superpose eq29707 eq16
    | exact resolve eq16 eq29707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30059 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq29707
       grind)
    | exact superpose eq29707 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq29707
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq29707
       grind)
    | exact resolve eq13 eq29707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29707
  have eq30061 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq30059
  have eq30065 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30061
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq30061
    | exact resolve eq30061 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30061
  have eq30412 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30058
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq30058
    | exact resolve eq30058 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22202 eq30058
  have eq30416 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30412
       have r₂ := eq22722
       grind)
    | exact resolve eq30412 eq22722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22722 eq30412
  have eq30651 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30065
       have i₂ := eq22723
       grind)
    | exact superpose eq22723 eq30065
    | exact resolve eq30065 eq22723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22723 eq30065
  have eq30805 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq30651
  have eq30938 : x = (M.op x y) := by
    first
    | (have r₁ := eq30805
       have r₂ := eq30416
       grind)
    | exact resolve eq30805 eq30416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30416 eq30805
  have eq31318 : x ≠ x ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq30938
       grind)
    | exact superpose eq30938 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq30938
       grind)
    | exact resolve eq13 eq30938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31319 : x ≠ y ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq30938
       grind)
    | exact superpose eq30938 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq30938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31320 : y = (k y x) ∨ x = y := by grind
  clear eq31318
  have eq32423 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq91 x y
       have i₂ := eq31320
       grind)
    | exact superpose eq31320 eq91
    | (have j0 := eq91 x y
       grind)
    | exact resolve eq91 eq31320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq32449 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq32423
  have eq35832 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq32449
       grind)
    | exact superpose eq32449 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq32449
       grind)
    | exact resolve eq12 eq32449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32449
  have eq35834 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq35832
  have eq35835 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq35834
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq35834
    | exact resolve eq35834 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35834
  have eq36640 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq35835
       grind)
    | exact superpose eq35835 eq16
    | exact resolve eq16 eq35835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35835
  have eq36649 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq36640
       have i₂ := eq30938
       grind)
    | exact superpose eq30938 eq36640
    | exact resolve eq36640 eq30938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36640
  have eq36650 : (σ x) = (σ (k y x)) ∨ x = y := by grind
  clear eq36649
  have eq37086 : (k y x) = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq36650
       grind)
    | exact superpose eq36650 eq10
    | exact resolve eq10 eq36650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36650
  have eq37298 : x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq37086
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq37086
    | exact resolve eq37086 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37086
  have eq37299 : x = (k y x) := by
    first
    | (have r₁ := eq37298
       have r₂ := eq31319
       grind)
    | exact resolve eq37298 eq31319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31319 eq37298
  have eq37676 : x = y ∨ x = y := by
    first
    | (have i₁ := eq31320
       have i₂ := eq37299
       grind)
    | exact superpose eq37299 eq31320
    | exact resolve eq31320 eq37299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31320
  have eq37707 : x = y := by grind
  clear eq37676
  have eq38143 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37707
       grind)
    | exact superpose eq37707 eq16
    | exact resolve eq16 eq37707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38144 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq37707
       grind)
    | exact superpose eq37707 eq84
    | exact resolve eq84 eq37707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq38176 : x = (M.op x x) := by
    first
    | (have i₁ := eq30938
       have i₂ := eq37707
       grind)
    | exact superpose eq37707 eq30938
    | exact resolve eq30938 eq37707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30938
  have eq38178 : x = (k x x) := by
    first
    | (have i₁ := eq37299
       have i₂ := eq37707
       grind)
    | exact superpose eq37707 eq37299
    | exact resolve eq37299 eq37707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37299 eq37707
  have eq38207 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq38144
  have eq38208 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq38207
       have i₂ := eq38178
       grind)
    | exact superpose eq38178 eq38207
    | exact resolve eq38207 eq38178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38178 eq38207
  have eq38209 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq38143
       have i₂ := eq38176
       grind)
    | exact superpose eq38176 eq38143
    | exact resolve eq38143 eq38176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38143
  have eq38210 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq38208
       have i₂ := eq38176
       grind)
    | exact superpose eq38176 eq38208
    | exact resolve eq38208 eq38176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38176 eq38208
  have eq38211 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq38210
  have eq38212 : False := by grind
  exact eq38212

/-- `Equation614`: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation614 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law614 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law614.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq78 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq16
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq374 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq405 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq374
    | (have j0 := eq374 X0 X1
       grind)
    | exact resolve eq374 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq800 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq78
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq78
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq78
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq78 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq801 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq800
  have eq4278 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq801
       grind)
    | exact superpose eq801 eq16
    | exact resolve eq16 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4279 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq801
       grind)
    | exact superpose eq801 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq801
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq801
       grind)
    | exact resolve eq13 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq4280 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4279
  have eq4281 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4280
  have eq4283 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4281
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4281
    | exact resolve eq4281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4281
  have eq6994 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq405 y x
       have i₂ := eq4283
       grind)
    | exact superpose eq4283 eq405
    | (have j0 := eq405 y x
       grind)
    | exact resolve eq405 eq4283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq6996 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq4283
       grind)
    | exact superpose eq4283 eq10
    | exact resolve eq10 eq4283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4283
  have eq7034 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6994
  have eq7060 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6996
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6996
    | exact resolve eq6996 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6996
  have eq7061 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7034
       have r₂ := eq4278
       grind)
    | exact resolve eq7034 eq4278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278 eq7034
  have eq7064 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq7060
       have r₂ := eq13 x y
       grind)
    | exact resolve eq7060 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7060
  have eq7477 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq80 x y
       have i₂ := eq7064
       grind)
    | exact superpose eq7064 eq80
    | (have j0 := eq80 x y
       grind)
    | exact resolve eq80 eq7064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq7064
  have eq7480 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7477
  have eq7481 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7480
  have eq7709 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq7481
       grind)
    | exact superpose eq7481 eq16
    | exact resolve eq16 eq7481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7481
  have eq7892 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7709
       have i₂ := eq7061
       grind)
    | exact superpose eq7061 eq7709
    | exact resolve eq7709 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7061 eq7709
  have eq7893 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7892
  have eq7894 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq7893
  have eq8062 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7894
       grind)
    | exact superpose eq7894 eq10
    | exact resolve eq10 eq7894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7894
  have eq8130 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8062
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8062
    | exact resolve eq8062 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8062
  have eq8131 : x = y := by grind
  clear eq8130
  have eq8277 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8131
       grind)
    | exact superpose eq8131 eq16
    | exact resolve eq16 eq8131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8131
  have eq8278 : False := by grind
  exact eq8278

/-- `Equation614`: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation614 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law614 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law614.models_iff G M).mp hM
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
  have eq44 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq57 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq45 x y
       grind)
    | exact superpose eq45 eq16
    | (have j1 := eq45 x y
       grind)
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq303 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44
    | exact resolve eq44 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq335 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq303
    | (have j0 := eq303 X0 X1
       grind)
    | exact resolve eq303 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq697 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq57
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq57
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq57
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq57
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq698 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq697
  have eq3751 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq698
       grind)
    | exact superpose eq698 eq16
    | exact resolve eq16 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3752 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq698
       grind)
    | exact superpose eq698 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq698
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq698
       grind)
    | exact resolve eq13 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq3753 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3752
  have eq3754 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3753
  have eq3756 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3754
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3754
    | exact resolve eq3754 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3754
  have eq6422 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq335 x y
       have i₂ := eq3756
       grind)
    | exact superpose eq3756 eq335
    | (have j0 := eq335 x y
       grind)
    | exact resolve eq335 eq3756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq6424 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq3756
       grind)
    | exact superpose eq3756 eq10
    | exact resolve eq10 eq3756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3756
  have eq6463 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6422
  have eq6491 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6424
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6424
    | exact resolve eq6424 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6424
  have eq6492 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6463
       have r₂ := eq3751
       grind)
    | exact resolve eq6463 eq3751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3751 eq6463
  have eq6495 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq6491
       have r₂ := eq13 y x
       grind)
    | exact resolve eq6491 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6491
  have eq6841 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59 x y
       have i₂ := eq6495
       grind)
    | exact superpose eq6495 eq59
    | (have j0 := eq59 x y
       grind)
    | exact resolve eq59 eq6495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq6495
  have eq6844 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6841
  have eq6845 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6844
  have eq7047 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq6845
       grind)
    | exact superpose eq6845 eq16
    | exact resolve eq16 eq6845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6845
  have eq7257 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7047
       have i₂ := eq6492
       grind)
    | exact superpose eq6492 eq7047
    | exact resolve eq7047 eq6492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6492 eq7047
  have eq7258 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7257
  have eq7259 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq7258
  have eq7419 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7259
       grind)
    | exact superpose eq7259 eq10
    | exact resolve eq10 eq7259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7259
  have eq7492 : x = y ∨ x = y := by
    first
    | (have i₁ := eq7419
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7419
    | exact resolve eq7419 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7419
  have eq7493 : x = y := by grind
  clear eq7492
  have eq7658 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7493
       grind)
    | exact superpose eq7493 eq16
    | exact resolve eq16 eq7493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7493
  have eq7659 : False := by grind
  exact eq7659

/-- `Equation616`: `x = x ◇ (x ◇ ((x ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_x_pxx_x_pxy_Equation616 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law616 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law616.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq27 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq27 (σ X0)
       grind)
    | exact superpose eq27 eq15
    | exact resolve eq15 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29 X0
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq29
    | exact resolve eq29 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq29
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq99 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq12
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq63
    | (have j0 := eq63 (σ X0) (σ X1)
       grind)
    | exact resolve eq63 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq179 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq173 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq173 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq173 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq173 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq188 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X1
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq148
    | (have j0 := eq148 X0 X1
       grind)
    | exact resolve eq148 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq314 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq318 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq314 X0 X1
       have j1 := eq188 X0 X1
       grind)
    | (have r₁ := eq314 X0 X1
       have r₂ := eq188 X0 X1
       grind)
    | exact resolve eq314 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq314
  have eq355 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq179 X0 (τ X1)
       grind)
    | exact superpose eq179 eq18
    | (have j1 := eq179 X0 (τ X1)
       grind)
    | exact resolve eq18 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq179
  have eq887 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq318 x y
       grind)
    | exact superpose eq318 eq16
    | (have j1 := eq318 x y
       grind)
    | exact resolve eq16 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq910 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq318 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq2253 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq355 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq355
    | exact resolve eq355 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq2327 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2253 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2253
    | (have j0 := eq2253 X0 X1
       grind)
    | exact resolve eq2253 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253
  have eq3387 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq887
       have i₂ := eq2327 y x
       grind)
    | exact superpose eq2327 eq887
    | (have j1 := eq2327 (σ y) (σ x)
       grind)
    | (have r₁ := eq887
       have r₂ := eq2327 y x
       grind)
    | exact resolve eq887 eq2327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq3388 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3387
  have eq3489 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3388
       grind)
    | exact superpose eq3388 eq16
    | exact resolve eq16 eq3388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3492 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3388
       grind)
    | exact superpose eq3388 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3388
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3388
       grind)
    | exact resolve eq13 eq3388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3496 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3492
  have eq3499 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3496
       have i₂ := eq32 x
       grind)
    | exact superpose eq32 eq3496
    | exact resolve eq3496 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3496
  have eq3503 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3499
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3499
    | exact resolve eq3499 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3499
  have eq18562 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2327 y x
       have i₂ := eq3503
       grind)
    | exact superpose eq3503 eq2327
    | (have j0 := eq2327 y x
       grind)
    | exact resolve eq2327 eq3503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3503
  have eq18645 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq18562
  have eq18678 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18645
       have r₂ := eq3489
       grind)
    | exact resolve eq18645 eq3489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18645
  have eq18962 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq18678
       grind)
    | exact superpose eq18678 eq10
    | exact resolve eq10 eq18678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18678
  have eq19060 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18962
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18962
    | exact resolve eq18962 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18962
  have eq19336 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19060
       grind)
    | exact superpose eq19060 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19060
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq19060
       grind)
    | exact resolve eq13 eq19060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19346 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by grind
  clear eq19336
  have eq19347 : x = (k x y) ∨ x = (M.op x x) := by grind
  clear eq19346
  have eq19840 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq910 x y
       have i₂ := eq19347
       grind)
    | exact superpose eq19347 eq910
    | (have j0 := eq910 x y
       grind)
    | exact resolve eq910 eq19347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19347
  have eq19863 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq19840
  have eq20941 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19863
       grind)
    | exact superpose eq19863 eq16
    | exact resolve eq16 eq19863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19863
  have eq21298 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20941
       have i₂ := eq19060
       grind)
    | exact superpose eq19060 eq20941
    | exact resolve eq20941 eq19060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19060 eq20941
  have eq21299 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by grind
  clear eq21298
  have eq21300 : x = (M.op x x) := by grind
  clear eq21299
  have eq21592 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq21300
       grind)
    | exact superpose eq21300 eq12
    | exact resolve eq12 eq21300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21598 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (σ x) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq99 x x
       have i₂ := eq21300
       grind)
    | exact superpose eq21300 eq99
    | exact resolve eq99 eq21300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq21300
  have eq22532 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21598 (σ y)
       have i₂ := eq3388
       grind)
    | exact superpose eq3388 eq21598
    | (have j0 := eq21598 (σ y)
       grind)
    | (have r₁ := eq21598 (σ y)
       have r₂ := eq3388
       grind)
    | exact resolve eq21598 eq3388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388 eq21598
  have eq22572 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22532
  have eq22590 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22572
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq22572
    | exact resolve eq22572 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22572
  have eq22774 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2327 y x
       have i₂ := eq22590
       grind)
    | exact superpose eq22590 eq2327
    | (have j0 := eq2327 y x
       grind)
    | exact resolve eq2327 eq22590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327
  have eq22777 : (k x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq22590
       grind)
    | exact superpose eq22590 eq10
    | exact resolve eq10 eq22590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22590
  have eq22867 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq22774
  have eq22902 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22777
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22777
    | exact resolve eq22777 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22777
  have eq22903 : x = (M.op x y) := by
    first
    | (have r₁ := eq22867
       have r₂ := eq3489
       grind)
    | exact resolve eq22867 eq3489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3489 eq22867
  have eq22913 : x = (k x y) := by
    first
    | (have j1 := eq21592 y
       grind)
    | (have r₁ := eq22902
       have r₂ := eq21592 y
       grind)
    | exact resolve eq22902 eq21592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21592 eq22902
  have eq23308 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq910 x y
       have i₂ := eq22913
       grind)
    | exact superpose eq22913 eq910
    | (have j0 := eq910 x y
       grind)
    | exact resolve eq910 eq22913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910 eq22913
  have eq23332 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23308
  have eq24450 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23332
       grind)
    | exact superpose eq23332 eq16
    | exact resolve eq16 eq23332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23332
  have eq24477 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq24450
       have i₂ := eq22903
       grind)
    | exact superpose eq22903 eq24450
    | exact resolve eq24450 eq22903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22903 eq24450
  have eq24478 : False := by grind
  exact eq24478

/-- `Equation616`: `x = x ◇ (x ◇ ((x ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_y_pxx_y_pxy_Equation616 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law616 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law616.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op X0 X1) X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq23 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op (M.op X0 x) X0))
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq27 (σ X0)
       grind)
    | exact superpose eq27 eq15
    | exact resolve eq15 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29 X0
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq29
    | exact resolve eq29 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq29
  have eq50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq89 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq23 (σ X0)
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq23
    | exact resolve eq23 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq61
    | (have j0 := eq61 (σ X0) (σ X1)
       grind)
    | exact resolve eq61 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq133 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq130 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq130 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq130 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq130 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq130 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq140 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 X1
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq110
    | (have j0 := eq110 X0 X1
       grind)
    | exact resolve eq110 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq268 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq270 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       have j1 := eq140 X0 X1
       grind)
    | (have r₁ := eq268 X0 X1
       have r₂ := eq140 X0 X1
       grind)
    | exact resolve eq268 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq268
  have eq329 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq133 (τ X0) X1
       grind)
    | exact superpose eq133 eq17
    | (have j1 := eq133 (τ X0) X1
       grind)
    | exact resolve eq17 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq133
  have eq844 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq270 x y
       grind)
    | exact superpose eq270 eq16
    | (have j1 := eq270 x y
       grind)
    | exact resolve eq16 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq866 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq270 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq1999 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq329 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq329
    | exact resolve eq329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq2089 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1999 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1999
    | (have j0 := eq1999 X0 X1
       grind)
    | exact resolve eq1999 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999
  have eq2960 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq844
       have i₂ := eq2089 x y
       grind)
    | exact superpose eq2089 eq844
    | (have j1 := eq2089 (σ x) (σ y)
       grind)
    | (have r₁ := eq844
       have r₂ := eq2089 x y
       grind)
    | exact resolve eq844 eq2089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq2961 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2960
  have eq3069 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2961
       grind)
    | exact superpose eq2961 eq16
    | exact resolve eq16 eq2961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3072 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq2961
       grind)
    | exact superpose eq2961 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2961
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2961
       grind)
    | exact resolve eq13 eq2961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3077 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3072
  have eq3079 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3077
       have i₂ := eq32 x
       grind)
    | exact superpose eq32 eq3077
    | exact resolve eq3077 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3077
  have eq3083 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3079
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3079
    | exact resolve eq3079 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3079
  have eq12337 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2089 x y
       have i₂ := eq3083
       grind)
    | exact superpose eq3083 eq2089
    | (have j0 := eq2089 x y
       grind)
    | exact resolve eq2089 eq3083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089 eq3083
  have eq12418 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq12337
  have eq12450 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12418
       have r₂ := eq3069
       grind)
    | exact resolve eq12418 eq3069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3069 eq12418
  have eq12836 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq12450
       grind)
    | exact superpose eq12450 eq10
    | exact resolve eq10 eq12450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12450
  have eq12929 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12836
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq12836
    | exact resolve eq12836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12836
  have eq13307 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq12929
       grind)
    | exact superpose eq12929 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12929
       grind)
    | exact resolve eq13 eq12929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13312 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by grind
  clear eq13307
  have eq13313 : y = (k x y) ∨ y = (M.op x x) := by grind
  clear eq13312
  have eq13690 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq866 x y
       have i₂ := eq13313
       grind)
    | exact superpose eq13313 eq866
    | (have j0 := eq866 x y
       grind)
    | exact resolve eq866 eq13313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866 eq13313
  have eq13712 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq13690
  have eq14447 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13712
       grind)
    | exact superpose eq13712 eq16
    | exact resolve eq16 eq13712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13712
  have eq14816 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14447
       have i₂ := eq12929
       grind)
    | exact superpose eq12929 eq14447
    | exact resolve eq14447 eq12929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12929 eq14447
  have eq14817 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq14816
  have eq14818 : y = (M.op x x) := by grind
  clear eq14817
  have eq15217 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq23 x
       have i₂ := eq14818
       grind)
    | exact superpose eq14818 eq23
    | exact resolve eq23 eq14818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq15225 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq89 x
       have i₂ := eq14818
       grind)
    | exact superpose eq14818 eq89
    | exact resolve eq89 eq14818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq14818
  have eq16715 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15225
       have i₂ := eq2961
       grind)
    | exact superpose eq2961 eq15225
    | exact resolve eq15225 eq2961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15225
  have eq18103 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2961
       have i₂ := eq16715
       grind)
    | exact superpose eq16715 eq2961
    | exact resolve eq2961 eq16715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2961 eq16715
  have eq18147 : y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq18103
  have eq18578 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15217
       have i₂ := eq18147
       grind)
    | exact superpose eq18147 eq15217
    | exact resolve eq15217 eq18147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15217
  have eq18904 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18147
       have i₂ := eq18578
       grind)
    | exact superpose eq18578 eq18147
    | exact resolve eq18147 eq18578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18147 eq18578
  have eq18920 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq18904
  have eq19453 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18920
       grind)
    | exact superpose eq18920 eq10
    | exact resolve eq10 eq18920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18920
  have eq19557 : x = y ∨ x = y := by
    first
    | (have i₁ := eq19453
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19453
    | exact resolve eq19453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19453
  have eq19558 : x = y := by grind
  clear eq19557
  have eq19794 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19558
       grind)
    | exact superpose eq19558 eq16
    | exact resolve eq16 eq19558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19558
  have eq19830 : False := by grind
  exact eq19830

/-- `Equation616`: `x = x ◇ (x ◇ ((x ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_pxx_pxy_Equation616 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law616 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law616.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = M.op a a :=
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
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq28 (σ X0)
       grind)
    | exact superpose eq28 eq15
    | exact resolve eq15 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq30
    | exact resolve eq30 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq30
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | (have j0 := eq38 X0 X1
       grind)
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq47
    | (have j0 := eq47 (σ (k X0 X1)) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq47 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq83 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq80 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq80 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq80 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq80 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq192 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq88 (k X0 X1) (M.op X0 X0)
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq88 (M.op X0 X0) (k X0 X1)
       grind)
    | exact resolve eq192 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq192
  have eq330 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq83 (τ X0) X1
       grind)
    | exact superpose eq83 eq18
    | (have j1 := eq83 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq83
  have eq654 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq199 x y
       grind)
    | exact superpose eq199 eq16
    | (have j1 := eq199 x y
       grind)
    | exact resolve eq16 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq795 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq330 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq330
    | exact resolve eq330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq842 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq795
    | (have j0 := eq795 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq1250 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq654
       have i₂ := eq842 x y
       grind)
    | exact superpose eq842 eq654
    | (have j1 := eq842 (σ x) (σ y)
       grind)
    | (have r₁ := eq654
       have r₂ := eq842 x y
       grind)
    | (have r₁ := eq654
       have r₂ := eq842 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq654
       have r₂ := eq842 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq654 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq842
  have eq1251 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1250
  have eq1337 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1251
       grind)
    | exact superpose eq1251 eq10
    | exact resolve eq10 eq1251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1374 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1337
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1337
    | exact resolve eq1337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1375 : x = y := by grind
  clear eq1374
  have eq1508 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1375
       grind)
    | exact superpose eq1375 eq16
    | exact resolve eq16 eq1375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1509 : False := by grind
  exact eq1509

/-- `Equation616`: `x = x ◇ (x ◇ ((x ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation616 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law616 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law616.models_iff G M).mp hM
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
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq28 (σ X0)
       grind)
    | exact superpose eq28 eq15
    | exact resolve eq15 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq30
    | exact resolve eq30 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq30
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | (have j0 := eq38 X0 X1
       grind)
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq47
    | (have j0 := eq47 (σ (k X0 X1)) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq47 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq83 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq80 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq80 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq80 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq80 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq192 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq88 (k X0 X1) (M.op X0 X0)
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq88 (M.op X0 X0) (k X0 X1)
       grind)
    | exact resolve eq192 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq192
  have eq330 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq83 (τ X0) X1
       grind)
    | exact superpose eq83 eq18
    | (have j1 := eq83 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq83
  have eq654 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq199 x y
       grind)
    | exact superpose eq199 eq16
    | (have j1 := eq199 x y
       grind)
    | exact resolve eq16 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq795 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq330 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq330
    | exact resolve eq330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq842 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq795
    | (have j0 := eq795 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq1250 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq654
       have i₂ := eq842 x y
       grind)
    | exact superpose eq842 eq654
    | (have j1 := eq842 (σ x) (σ y)
       grind)
    | (have r₁ := eq654
       have r₂ := eq842 x y
       grind)
    | (have r₁ := eq654
       have r₂ := eq842 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq654
       have r₂ := eq842 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq654 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq842
  have eq1251 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1250
  have eq1337 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1251
       grind)
    | exact superpose eq1251 eq10
    | exact resolve eq10 eq1251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1374 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1337
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1337
    | exact resolve eq1337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1375 : x = y := by grind
  clear eq1374
  have eq1508 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1375
       grind)
    | exact superpose eq1375 eq16
    | exact resolve eq16 eq1375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1509 : False := by grind
  exact eq1509

/-- `Equation616`: `x = x ◇ (x ◇ ((x ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_Equation616 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law616 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law616.models_iff G M).mp hM
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
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq26 (σ X0)
       grind)
    | exact superpose eq26 eq15
    | exact resolve eq15 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq28
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq45 (σ X0) (σ X1)
       grind)
    | exact superpose eq45 eq15
    | (have j1 := eq45 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq45 (τ X0) X1
       grind)
    | exact superpose eq45 eq18
    | (have j1 := eq45 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq45
  have eq208 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq208
    | (have j0 := eq208 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq208 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq599 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62 x y
       grind)
    | exact superpose eq62 eq16
    | (have j1 := eq62 x y
       grind)
    | exact resolve eq16 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq749 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq599
       have i₂ := eq235 x y
       grind)
    | exact superpose eq235 eq599
    | (have j1 := eq235 (σ x) (σ y)
       grind)
    | (have r₁ := eq599
       have r₂ := eq235 x y
       grind)
    | (have r₁ := eq599
       have r₂ := eq235 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq599
       have r₂ := eq235 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq599 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq599
  have eq750 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq749
  have eq857 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq750
       grind)
    | exact superpose eq750 eq10
    | exact resolve eq10 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq893 : x = y ∨ x = y := by
    first
    | (have i₁ := eq857
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq857
    | exact resolve eq857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq894 : x = y := by grind
  clear eq893
  have eq945 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq894
       grind)
    | exact superpose eq894 eq16
    | exact resolve eq16 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq946 : False := by grind
  exact eq946

/-- `Equation616`: `x = x ◇ (x ◇ ((x ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation616 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law616 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law616.models_iff G M).mp hM
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
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq26 (σ X0)
       grind)
    | exact superpose eq26 eq15
    | exact resolve eq15 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq28
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28
  have eq37 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X2) = (k X1 X2) ∨ X1 = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ X0 = X2 := by
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
  have eq46 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ X0 = X2 := by
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X1 X1 X2
       have j1 := eq46 X1 X1 X2
       grind)
    | (have r₁ := eq37 X0 X1 X2
       have r₂ := eq46 X0 X1 X2
       grind)
    | (have r₁ := eq37 X1 X0 X2
       have r₂ := eq46 X0 X1 X2
       grind)
    | (have r₁ := eq37 X0 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq46 X0 X1 X2
       grind)
    | exact resolve eq37 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq46
  have eq108 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq109 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq110 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq203 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq110 (σ X0) (σ X1)
       grind)
    | exact superpose eq110 eq15
    | (have j1 := eq110 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq110 (τ X0) X1
       grind)
    | exact superpose eq110 eq18
    | (have j1 := eq110 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq110
  have eq542 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq205 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq205
    | exact resolve eq205 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq576 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq542 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq542
    | (have j0 := eq542 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq542 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq1511 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq203 x y
       grind)
    | exact superpose eq203 eq16
    | (have j1 := eq203 x y
       grind)
    | exact resolve eq16 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq1615 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1511
       have i₂ := eq576 x y
       grind)
    | exact superpose eq576 eq1511
    | (have j1 := eq576 (σ x) (σ y)
       grind)
    | (have r₁ := eq1511
       have r₂ := eq576 x y
       grind)
    | (have r₁ := eq1511
       have r₂ := eq576 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1511
       have r₂ := eq576 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1511 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq1511
  have eq1616 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1615
  have eq1700 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1616
       grind)
    | exact superpose eq1616 eq10
    | exact resolve eq10 eq1616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616
  have eq1742 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1700
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1700
    | exact resolve eq1700 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700
  have eq1743 : x = y := by grind
  clear eq1742
  have eq1817 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1743
       grind)
    | exact superpose eq1743 eq16
    | exact resolve eq16 eq1743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1818 : False := by grind
  exact eq1818

/-- `Equation616`: `x = x ◇ (x ◇ ((x ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_pyx_pxy_Equation616 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law616 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law616.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op X0 X1) X0))) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq71 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq30 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq30 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq30 X0 X1
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (M.op (σ X1) (M.op (σ X0) (σ X1)))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X1) (σ X0)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq30 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq30 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq30 X0 X1
       grind)
    | exact resolve eq12 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq77 : ∀ X0 X1 : G, (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq78 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq79 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq283 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31
    | exact resolve eq31 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq319 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq283 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq283
    | (have j0 := eq283 X0 X1
       grind)
    | exact resolve eq283 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq440 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq75 (τ X0) (τ X1)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq75
    | (have j0 := eq75 (τ X0) (τ X1)
       grind)
    | exact resolve eq75 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq440 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq440
    | (have j0 := eq440 X0 X1
       grind)
    | exact resolve eq440 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq450 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq447
    | (have j0 := eq447 X0 X1
       grind)
    | exact resolve eq447 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq452 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq450
    | (have j0 := eq450 X0 X1
       grind)
    | exact resolve eq450 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq453 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq452 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq452
    | (have j0 := eq452 X0 X1
       grind)
    | exact resolve eq452 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq454 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq453 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq453
    | (have j0 := eq453 X0 X1
       grind)
    | exact resolve eq453 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq455 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq454 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq454
    | (have j0 := eq454 X0 X1
       grind)
    | exact resolve eq454 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq510 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq16
    | (have j1 := eq83 x y
       grind)
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq588 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X1)))) ∨ (σ (k X0 X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq72
    | (have j0 := eq72 X1 X0
       have j1 := eq84 X1 X0
       grind)
    | exact resolve eq72 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq84
  have eq739 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X1)))) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq733 X0 X1
       have j1 := eq589 X1 X0
       grind)
    | (have r₁ := eq733 X0 X1
       have r₂ := eq589 X0 X1
       grind)
    | (have r₁ := eq733 X1 X0
       have r₂ := eq589 X0 X1
       grind)
    | exact resolve eq733 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq742 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X1)))) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq739 X0 X1
       have j1 := eq590 X1 X0
       grind)
    | (have r₁ := eq739 X1 X0
       have r₂ := eq590 X0 X1
       grind)
    | exact resolve eq739 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq739
  have eq4304 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq510
       have i₂ := eq319 x y
       grind)
    | exact superpose eq319 eq510
    | (have j1 := eq319 x y
       grind)
    | (have r₁ := eq510
       have r₂ := eq319 x y
       grind)
    | exact resolve eq510 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq510
  have eq4305 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq4304
  have eq6535 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq589 (τ X1) (τ X0)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq589
    | (have j0 := eq589 (τ X1) (τ X0)
       grind)
    | exact resolve eq589 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6589 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6535 X0 X1
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq6535
    | (have j0 := eq6535 X0 X1
       grind)
    | exact resolve eq6535 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6535
  have eq6635 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6589 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6589
    | (have j0 := eq6589 X0 X1
       grind)
    | exact resolve eq6589 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6589
  have eq6674 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6635 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6635
    | (have j0 := eq6635 X0 X1
       grind)
    | (have r₁ := eq6635 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq6635 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6635
  have eq6710 : ∀ X0 X1 : G, (M.op (σ (τ X1)) (σ (τ X0))) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6674 X0 X1
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq6674
    | (have j0 := eq6674 X0 X1
       grind)
    | exact resolve eq6674 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6674
  have eq6742 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 (σ (τ X0))) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6710 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6710
    | (have j0 := eq6710 X0 X1
       grind)
    | exact resolve eq6710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6710
  have eq6774 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6742 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6742
    | (have j0 := eq6742 X0 X1
       grind)
    | exact resolve eq6742 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6742
  have eq6782 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6774 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6774
    | (have j0 := eq6774 X0 X1
       grind)
    | exact resolve eq6774 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6774
  have eq6790 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6782 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6782
    | (have j0 := eq6782 X0 X1
       grind)
    | exact resolve eq6782 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6782
  have eq13958 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op (σ (τ X0)) (σ (τ (k X0 X1))))) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq742 (τ X0) (τ X1)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq742
    | (have j0 := eq742 (τ X0) (τ X1)
       grind)
    | exact resolve eq742 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq742
  have eq14049 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op (σ (τ X0)) (k X0 X1))) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13958 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq13958
    | (have j0 := eq13958 X0 X1
       grind)
    | exact resolve eq13958 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13958
  have eq14085 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (k X0 X1))) = X0 ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14049 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14049
    | (have j0 := eq14049 X0 X1
       grind)
    | exact resolve eq14049 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14049
  have eq14114 : ∀ X0 X1 : G, (M.op (σ (τ X1)) (σ (τ X0))) = (k (σ (τ X1)) X0) ∨ (M.op X0 (M.op X0 (k X0 X1))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14085 X0 X1
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq14085
    | (have j0 := eq14085 X0 X1
       grind)
    | exact resolve eq14085 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq14085
  have eq14139 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 (σ (τ X0))) ∨ (M.op X0 (M.op X0 (k X0 X1))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14114 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14114
    | (have j0 := eq14114 X0 X1
       grind)
    | exact resolve eq14114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14114
  have eq14163 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 (M.op X0 (k X0 X1))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14139 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14139
    | (have j0 := eq14139 X0 X1
       grind)
    | exact resolve eq14139 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14139
  have eq14181 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 (M.op X0 (k X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14163 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14163
    | (have j0 := eq14163 X0 X1
       grind)
    | exact resolve eq14163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14163
  have eq14195 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (k X0 X1))) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14181 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq14181
    | (have j0 := eq14181 X0 X1
       grind)
    | exact resolve eq14181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14181
  have eq173760 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq4305
       grind)
    | exact superpose eq4305 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq4305
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq4305
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq4305
       grind)
    | exact resolve eq12 eq4305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4305
  have eq173761 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq173760
  have eq173762 : (σ x) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq173761
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq173761
    | exact resolve eq173761 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173761
  have eq173771 : (k y x) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq173762
       grind)
    | exact superpose eq173762 eq10
    | exact resolve eq10 eq173762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173762
  have eq173815 : x = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq173771
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq173771
    | exact resolve eq173771 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173771
  have eq173817 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq455 y x
       grind)
    | (have r₁ := eq173815
       have r₂ := eq455 y x
       grind)
    | exact resolve eq173815 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq173815
  have eq173833 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq173817
       grind)
    | exact superpose eq173817 eq10
    | exact resolve eq10 eq173817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173817
  have eq173914 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq173833
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq173833
    | exact resolve eq173833 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173833
  have eq173915 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq173914
  have eq173936 : x ≠ x ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq173915
       grind)
    | exact superpose eq173915 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq173915
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq173915
       grind)
    | exact resolve eq12 eq173915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173937 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq173915
       grind)
    | exact superpose eq173915 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq173915
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq173915
       grind)
    | exact resolve eq13 eq173915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173941 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq173937
  have eq173942 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq173941
  have eq173943 : y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq173936
  have eq173964 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq588 x y
       have i₂ := eq173943
       grind)
    | exact superpose eq173943 eq588
    | (have j0 := eq588 x y
       grind)
    | exact resolve eq588 eq173943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq174013 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq173964
  have eq230718 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq174013
       grind)
    | exact superpose eq174013 eq16
    | exact resolve eq16 eq174013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174013
  have eq230741 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq230718
       have i₂ := eq173942
       grind)
    | exact superpose eq173942 eq230718
    | exact resolve eq230718 eq173942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173942 eq230718
  have eq230751 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq230741
  have eq230752 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq230751
  have eq230760 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq230752
       grind)
    | exact superpose eq230752 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq230752
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq230752
       grind)
    | exact resolve eq12 eq230752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230752
  have eq230764 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq230760
  have eq230768 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq230764
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq230764
    | exact resolve eq230764 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230764
  have eq230797 : (k y x) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq230768
       grind)
    | exact superpose eq230768 eq10
    | exact resolve eq10 eq230768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230768
  have eq231002 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq230797
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq230797
    | exact resolve eq230797 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230797
  have eq231007 : x = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq231002
       have r₂ := eq12 y x
       grind)
    | exact resolve eq231002 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231002
  have eq231019 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq75 y x
       have i₂ := eq231007
       grind)
    | exact superpose eq231007 eq75
    | (have j0 := eq75 y x
       grind)
    | exact resolve eq75 eq231007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq231028 : (σ x) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq589 y x
       have i₂ := eq231007
       grind)
    | exact superpose eq231007 eq589
    | (have j0 := eq589 y x
       grind)
    | exact resolve eq589 eq231007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq231064 : x ≠ (k x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6790 y x
       have i₂ := eq231007
       grind)
    | exact superpose eq231007 eq6790
    | (have j0 := eq6790 y x
       grind)
    | exact resolve eq6790 eq231007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6790
  have eq231067 : y = (M.op y (M.op y x)) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14195 y x
       have i₂ := eq231007
       grind)
    | exact superpose eq231007 eq14195
    | (have j0 := eq14195 y x
       grind)
    | exact resolve eq14195 eq231007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14195
  have eq231086 : (σ x) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq231028
  have eq231090 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq231019
  have eq233326 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq231090
       grind)
    | exact superpose eq231090 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq231090
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq231090
       grind)
    | exact resolve eq12 eq231090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233327 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq231090
       grind)
    | exact superpose eq231090 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq231090
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq231090
       grind)
    | exact resolve eq13 eq231090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231090
  have eq233328 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq233327
  have eq233329 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq233328
  have eq233330 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq233326
  have eq233333 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq233329
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq233329
    | exact resolve eq233329 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233329
  have eq233334 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq233330
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq233330
    | exact resolve eq233330 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233330
  have eq233337 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq233333
       have i₂ := eq231007
       grind)
    | exact superpose eq231007 eq233333
    | exact resolve eq233333 eq231007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231007 eq233333
  have eq233341 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq233334
       grind)
    | exact superpose eq233334 eq16
    | exact resolve eq16 eq233334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233334
  have eq235913 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq233337
       grind)
    | exact superpose eq233337 eq16
    | exact resolve eq16 eq233337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233337
  have eq245220 : x ≠ y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq231064
       have i₂ := eq173943
       grind)
    | exact superpose eq173943 eq231064
    | exact resolve eq231064 eq173943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231064
  have eq245221 : x ≠ y ∨ y = (M.op x y) := by grind
  clear eq245220
  have eq275691 : y = (M.op y x) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq231067
       have i₂ := eq173915
       grind)
    | exact superpose eq173915 eq231067
    | exact resolve eq231067 eq173915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231067
  have eq275703 : (M.op x y) = (k x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq275691
  have eq275712 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq173943
       have i₂ := eq275703
       grind)
    | exact superpose eq275703 eq173943
    | exact resolve eq173943 eq275703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173943 eq275703
  have eq275924 : y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq275712
  have eq275938 : x = y ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq173915
       have i₂ := eq275924
       grind)
    | exact superpose eq275924 eq173915
    | exact resolve eq173915 eq275924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173915 eq275924
  have eq275965 : x = y ∨ y = (M.op x y) := by grind
  clear eq275938
  have eq275970 : y = (M.op x y) := by
    first
    | (have r₁ := eq275965
       have r₂ := eq245221
       grind)
    | exact resolve eq275965 eq245221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245221 eq275965
  have eq275978 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq233341
       have i₂ := eq275970
       grind)
    | exact superpose eq275970 eq233341
    | exact resolve eq233341 eq275970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233341
  have eq275980 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq235913
       have i₂ := eq275970
       grind)
    | exact superpose eq275970 eq235913
    | exact resolve eq235913 eq275970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235913
  have eq275996 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq275980
  have eq275997 : (σ y) = (σ (k x y)) := by grind
  clear eq275978
  have eq276029 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq231086
       have i₂ := eq275997
       grind)
    | exact superpose eq275997 eq231086
    | exact resolve eq231086 eq275997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231086
  have eq276045 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq275997
       grind)
    | exact superpose eq275997 eq10
    | exact resolve eq10 eq275997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275997
  have eq276303 : y = (k x y) := by
    first
    | (have i₁ := eq276045
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq276045
    | exact resolve eq276045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276045
  have eq276436 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq275996
       grind)
    | exact superpose eq275996 eq16
    | exact resolve eq16 eq275996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276486 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq47 (σ x) y
       have i₂ := eq275996
       grind)
    | exact superpose eq275996 eq47
    | (have j0 := eq47 (σ y) x
       grind)
    | exact resolve eq47 eq275996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq276533 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq276486
       have r₂ := eq276029
       grind)
    | exact resolve eq276486 eq276029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276029 eq276486
  have eq276572 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq276436
       have i₂ := eq275970
       grind)
    | exact superpose eq275970 eq276436
    | exact resolve eq276436 eq275970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275970 eq276436
  have eq276593 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq276533
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq276533
    | exact resolve eq276533 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276533
  have eq276640 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq276593
       have i₂ := eq276303
       grind)
    | exact superpose eq276303 eq276593
    | exact resolve eq276593 eq276303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276303 eq276593
  have eq279323 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = y := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq276640
       grind)
    | exact superpose eq276640 eq9
    | exact resolve eq9 eq276640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279333 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq279323
       have i₂ := eq275996
       grind)
    | exact superpose eq275996 eq279323
    | exact resolve eq279323 eq275996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275996 eq279323
  have eq280448 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq279333
       have i₂ := eq276640
       grind)
    | exact superpose eq276640 eq279333
    | exact resolve eq279333 eq276640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279333
  have eq280455 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq280448
  have eq280478 : (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq276640
       have i₂ := eq280455
       grind)
    | exact superpose eq280455 eq276640
    | exact resolve eq276640 eq280455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276640 eq280455
  have eq280525 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq280478
  have eq280564 : x = y := by
    first
    | (have r₁ := eq280525
       have r₂ := eq276572
       grind)
    | exact resolve eq280525 eq276572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280525
  have eq281253 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq276572
       have i₂ := eq280564
       grind)
    | exact superpose eq280564 eq276572
    | exact resolve eq276572 eq280564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276572 eq280564
  have eq281254 : False := by grind
  exact eq281254

/-- `Equation640`: `x = x ◇ (y ◇ ((y ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_y_pxx_y_pxy_Equation640 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law640 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law640.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq102 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq150 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq147 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq147 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq147 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq147 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq147 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq238 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq150 (σ X0) (σ X1)
       grind)
    | exact superpose eq150 eq15
    | (have j1 := eq150 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq150 (τ X0) X1
       grind)
    | exact superpose eq150 eq17
    | (have j1 := eq150 (τ X0) X1
       grind)
    | exact resolve eq17 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq150
  have eq1670 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq240 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq240
    | exact resolve eq240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq1749 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1670 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1670
    | (have j0 := eq1670 X0 X1
       grind)
    | exact resolve eq1670 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq2694 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq238 x y
       grind)
    | exact superpose eq238 eq16
    | (have j1 := eq238 x y
       grind)
    | exact resolve eq16 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2731 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq238 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq3804 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2694
       have i₂ := eq1749 x y
       grind)
    | exact superpose eq1749 eq2694
    | (have j1 := eq1749 (σ x) (σ y)
       grind)
    | (have r₁ := eq2694
       have r₂ := eq1749 x y
       grind)
    | exact resolve eq2694 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2694
  have eq3805 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3804
  have eq3951 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3805
       grind)
    | exact superpose eq3805 eq16
    | exact resolve eq16 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3955 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3805
       grind)
    | exact superpose eq3805 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3805
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3805
       grind)
    | exact resolve eq13 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3962 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3955
  have eq3967 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3962
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq3962
    | exact resolve eq3962 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3962
  have eq3972 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3967
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3967
    | exact resolve eq3967 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3967
  have eq10127 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1749 x y
       have i₂ := eq3972
       grind)
    | exact superpose eq3972 eq1749
    | (have j0 := eq1749 x y
       grind)
    | exact resolve eq1749 eq3972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3972
  have eq10178 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq10127
  have eq10209 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10178
       have r₂ := eq3951
       grind)
    | exact resolve eq10178 eq3951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10178
  have eq10523 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq10209
       grind)
    | exact superpose eq10209 eq10
    | exact resolve eq10 eq10209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10209
  have eq10584 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10523
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq10523
    | exact resolve eq10523 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10523
  have eq10878 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq10584
       grind)
    | exact superpose eq10584 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq10584
       grind)
    | exact resolve eq13 eq10584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10893 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by grind
  clear eq10878
  have eq10894 : y = (k x y) ∨ y = (M.op x x) := by grind
  clear eq10893
  have eq11213 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2731 x y
       have i₂ := eq10894
       grind)
    | exact superpose eq10894 eq2731
    | (have j0 := eq2731 x y
       grind)
    | exact resolve eq2731 eq10894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10894
  have eq11224 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq11213
  have eq11915 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11224
       grind)
    | exact superpose eq11224 eq16
    | exact resolve eq16 eq11224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11224
  have eq12299 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11915
       have i₂ := eq10584
       grind)
    | exact superpose eq10584 eq11915
    | exact resolve eq11915 eq10584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10584 eq11915
  have eq12300 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq12299
  have eq12301 : y = (M.op x x) := by grind
  clear eq12300
  have eq12637 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq12301
       grind)
    | exact superpose eq12301 eq12
    | exact resolve eq12 eq12301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12644 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) ∨ (σ y) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq102 x x
       have i₂ := eq12301
       grind)
    | exact superpose eq12301 eq102
    | exact resolve eq102 eq12301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq12301
  have eq14527 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12644 (σ y)
       have i₂ := eq3805
       grind)
    | exact superpose eq3805 eq12644
    | (have j0 := eq12644 (σ y)
       grind)
    | (have r₁ := eq12644 (σ y)
       have r₂ := eq3805
       grind)
    | exact resolve eq12644 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805 eq12644
  have eq14545 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14527
  have eq14553 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14545
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq14545
    | exact resolve eq14545 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14545
  have eq14816 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1749 x y
       have i₂ := eq14553
       grind)
    | exact superpose eq14553 eq1749
    | (have j0 := eq1749 x y
       grind)
    | exact resolve eq1749 eq14553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749
  have eq14820 : (k x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq14553
       grind)
    | exact superpose eq14553 eq10
    | exact resolve eq10 eq14553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14553
  have eq14876 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14816
  have eq14910 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14820
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq14820
    | exact resolve eq14820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14820
  have eq14911 : y = (M.op x y) := by
    first
    | (have r₁ := eq14876
       have r₂ := eq3951
       grind)
    | exact resolve eq14876 eq3951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3951 eq14876
  have eq14920 : y = (k x y) := by
    first
    | (have j1 := eq12637 y
       grind)
    | (have r₁ := eq14910
       have r₂ := eq12637 y
       grind)
    | exact resolve eq14910 eq12637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12637 eq14910
  have eq15146 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2731 x y
       have i₂ := eq14920
       grind)
    | exact superpose eq14920 eq2731
    | (have j0 := eq2731 x y
       grind)
    | exact resolve eq2731 eq14920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2731 eq14920
  have eq15157 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15146
  have eq15701 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15157
       grind)
    | exact superpose eq15157 eq16
    | exact resolve eq16 eq15157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15157
  have eq15742 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq15701
       have i₂ := eq14911
       grind)
    | exact superpose eq14911 eq15701
    | exact resolve eq15701 eq14911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14911 eq15701
  have eq15743 : False := by grind
  exact eq15743

/-- `Equation640`: `x = x ◇ (y ◇ ((y ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_pxx_pxy_Equation640 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law640 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law640.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = M.op a a :=
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq94 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq91 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq91 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq91 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq91 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq180 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq94 (σ X0) (σ X1)
       grind)
    | exact superpose eq94 eq15
    | (have j1 := eq94 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq94 (τ X0) X1
       grind)
    | exact superpose eq94 eq18
    | (have j1 := eq94 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq94
  have eq557 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq182
    | exact resolve eq182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq592 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq557 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq557
    | (have j0 := eq557 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq557 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq1659 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq180 x y
       grind)
    | exact superpose eq180 eq16
    | (have j1 := eq180 x y
       grind)
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1852 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1659
       have i₂ := eq592 x y
       grind)
    | exact superpose eq592 eq1659
    | (have j1 := eq592 (σ x) (σ y)
       grind)
    | (have r₁ := eq1659
       have r₂ := eq592 x y
       grind)
    | (have r₁ := eq1659
       have r₂ := eq592 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1659
       have r₂ := eq592 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1659 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq1659
  have eq1853 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1852
  have eq1895 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1853
       grind)
    | exact superpose eq1853 eq10
    | exact resolve eq10 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq1939 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1895
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1895
    | exact resolve eq1895 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895
  have eq1940 : x = y := by grind
  clear eq1939
  have eq2115 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1940
       grind)
    | exact superpose eq1940 eq16
    | exact resolve eq16 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq2116 : False := by grind
  exact eq2116

/-- `Equation640`: `x = x ◇ (y ◇ ((y ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation640 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law640 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law640.models_iff G M).mp hM
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq94 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq91 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq91 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq91 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq91 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq180 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq94 (σ X0) (σ X1)
       grind)
    | exact superpose eq94 eq15
    | (have j1 := eq94 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq94 (τ X0) X1
       grind)
    | exact superpose eq94 eq18
    | (have j1 := eq94 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq94
  have eq557 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq182
    | exact resolve eq182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq592 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq557 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq557
    | (have j0 := eq557 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq557 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq1659 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq180 x y
       grind)
    | exact superpose eq180 eq16
    | (have j1 := eq180 x y
       grind)
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1852 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1659
       have i₂ := eq592 x y
       grind)
    | exact superpose eq592 eq1659
    | (have j1 := eq592 (σ x) (σ y)
       grind)
    | (have r₁ := eq1659
       have r₂ := eq592 x y
       grind)
    | (have r₁ := eq1659
       have r₂ := eq592 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1659
       have r₂ := eq592 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1659 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq1659
  have eq1853 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1852
  have eq1895 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1853
       grind)
    | exact superpose eq1853 eq10
    | exact resolve eq10 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq1939 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1895
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1895
    | exact resolve eq1895 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895
  have eq1940 : x = y := by grind
  clear eq1939
  have eq2115 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1940
       grind)
    | exact superpose eq1940 eq16
    | exact resolve eq16 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq2116 : False := by grind
  exact eq2116

/-- `Equation640`: `x = x ◇ (y ◇ ((y ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation640 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law640 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law640.models_iff G M).mp hM
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
  have eq47 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ X1 = X2 ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
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
  have eq60 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X1 = X2 ∨ X0 = X2 := by
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
  have eq127 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq128 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq129 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq128 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq188 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq129 (σ X0) (σ X1)
       grind)
    | exact superpose eq129 eq15
    | (have j1 := eq129 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq129 (τ X0) X1
       grind)
    | exact superpose eq129 eq18
    | (have j1 := eq129 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq129
  have eq329 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq190 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq190
    | exact resolve eq190 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq352 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq329 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq329
    | (have j0 := eq329 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq329 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq1409 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq188 x y
       grind)
    | exact superpose eq188 eq16
    | (have j1 := eq188 x y
       grind)
    | exact resolve eq16 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq1509 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1409
       have i₂ := eq352 x y
       grind)
    | exact superpose eq352 eq1409
    | (have j1 := eq352 (σ x) (σ y)
       grind)
    | (have r₁ := eq1409
       have r₂ := eq352 x y
       grind)
    | (have r₁ := eq1409
       have r₂ := eq352 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1409
       have r₂ := eq352 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1409 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq1409
  have eq1510 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1509
  have eq1589 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1510
       grind)
    | exact superpose eq1510 eq10
    | exact resolve eq10 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510
  have eq1630 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1589
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1589
    | exact resolve eq1589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589
  have eq1631 : x = y := by grind
  clear eq1630
  have eq1704 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1631
       grind)
    | exact superpose eq1631 eq16
    | exact resolve eq16 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631
  have eq1705 : False := by grind
  exact eq1705

/-- `Equation640`: `x = x ◇ (y ◇ ((y ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation640 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law640 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law640.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq36 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq115 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq16
    | (have j1 := eq36 x y
       grind)
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq332 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq123 (τ X1) (τ X0)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq123
    | (have j0 := eq123 (τ X1) (τ X0)
       grind)
    | exact resolve eq123 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq332 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq332
    | (have j0 := eq332 X0 X1
       grind)
    | exact resolve eq332 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq342 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq339 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq339
    | (have j0 := eq339 X0 X1
       grind)
    | exact resolve eq339 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq344 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq342
    | (have j0 := eq342 X0 X1
       grind)
    | exact resolve eq342 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq345 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq344
    | (have j0 := eq344 X0 X1
       grind)
    | exact resolve eq344 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq346 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq345 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq345
    | (have j0 := eq345 X0 X1
       grind)
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq347 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq346 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq346
    | (have j0 := eq346 X0 X1
       grind)
    | exact resolve eq346 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq394 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq124 (τ X1) (τ X0)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq124
    | (have j0 := eq124 (τ X1) (τ X0)
       grind)
    | exact resolve eq124 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq402 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq394 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq394
    | (have j0 := eq394 X0 X1
       grind)
    | exact resolve eq394 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq405 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq402
    | (have j0 := eq402 X0 X1
       grind)
    | exact resolve eq402 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq407 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq405 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq405
    | (have j0 := eq405 X0 X1
       grind)
    | exact resolve eq405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq408 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq407 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq407
    | (have j0 := eq407 X0 X1
       grind)
    | exact resolve eq407 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq409 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq408 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq408
    | (have j0 := eq408 X0 X1
       grind)
    | exact resolve eq408 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq410 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq409
    | (have j0 := eq409 X0 X1
       grind)
    | exact resolve eq409 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq455 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq115
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq115 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq455
  have eq3961 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq456
       grind)
    | exact superpose eq456 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq456
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq456
       grind)
    | exact resolve eq12 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq3972 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3961
  have eq3973 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3972
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3972
    | exact resolve eq3972 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3972
  have eq21474 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3973
       grind)
    | exact superpose eq3973 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3973
       grind)
    | exact resolve eq12 eq3973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21475 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3973
       grind)
    | exact superpose eq3973 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3973
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3973
       grind)
    | exact resolve eq13 eq3973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3973
  have eq21489 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq21475
  have eq21493 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21489
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq21489
    | exact resolve eq21489 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21489
  have eq21494 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21474
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq21474
    | exact resolve eq21474 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21474
  have eq21495 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq21494
  have eq119648 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq21493
       grind)
    | exact superpose eq21493 eq10
    | exact resolve eq10 eq21493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21493
  have eq119689 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq119648
       have r₂ := eq21495
       grind)
    | exact resolve eq119648 eq21495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21495 eq119648
  have eq119707 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq119689
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq119689
    | exact resolve eq119689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119689
  have eq119708 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq410 y x
       grind)
    | (have r₁ := eq119707
       have r₂ := eq410 y x
       grind)
    | exact resolve eq119707 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq119707
  have eq119995 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq119708
       grind)
    | exact superpose eq119708 eq10
    | exact resolve eq10 eq119708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119708
  have eq120170 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq119995
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq119995
    | exact resolve eq119995 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119995
  have eq120171 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq347 y x
       grind)
    | (have r₁ := eq120170
       have r₂ := eq347 y x
       grind)
    | exact resolve eq120170 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq120170
  have eq120425 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq120171
       grind)
    | exact superpose eq120171 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq120171
       grind)
    | exact resolve eq12 eq120171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120437 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq120438 : x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq120425
  have eq120825 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq123 x y
       have i₂ := eq120438
       grind)
    | exact superpose eq120438 eq123
    | (have j0 := eq123 x y
       grind)
    | exact resolve eq123 eq120438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq121032 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq120825
  have eq125763 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq121032
       grind)
    | exact superpose eq121032 eq16
    | exact resolve eq16 eq121032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121032
  have eq126289 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq125763
       have i₂ := eq120171
       grind)
    | exact superpose eq120171 eq125763
    | exact resolve eq125763 eq120171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125763
  have eq126292 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq126289
  have eq126293 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq126292
       have r₂ := eq120437
       grind)
    | exact resolve eq126292 eq120437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126292
  have eq126535 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq126293
       grind)
    | exact superpose eq126293 eq16
    | exact resolve eq16 eq126293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126540 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq126293
       grind)
    | exact superpose eq126293 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq126293
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq126293
       grind)
    | exact resolve eq13 eq126293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126293
  have eq126547 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq126540
  have eq126552 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq126547
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq126547
    | exact resolve eq126547 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126547
  have eq126617 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq126535
       have i₂ := eq120171
       grind)
    | exact superpose eq120171 eq126535
    | exact resolve eq126535 eq120171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120171 eq126535
  have eq126621 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq126617
       have r₂ := eq120437
       grind)
    | exact resolve eq126617 eq120437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120437 eq126617
  have eq127134 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq126552
       have i₂ := eq120438
       grind)
    | exact superpose eq120438 eq126552
    | exact resolve eq126552 eq120438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120438 eq126552
  have eq127282 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq127134
  have eq127380 : x = (M.op x y) := by
    first
    | (have r₁ := eq127282
       have r₂ := eq126621
       grind)
    | exact resolve eq127282 eq126621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126621 eq127282
  have eq127664 : x ≠ y ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq127380
       grind)
    | exact superpose eq127380 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq127380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127665 : x ≠ x ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq127380
       grind)
    | exact superpose eq127380 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq127380
       grind)
    | exact resolve eq13 eq127380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127678 : y = (k y x) ∨ x = y := by grind
  clear eq127665
  have eq127993 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq124 x y
       have i₂ := eq127678
       grind)
    | exact superpose eq127678 eq124
    | (have j0 := eq124 x y
       grind)
    | exact resolve eq124 eq127678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128100 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq127993
  have eq130420 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq128100
       grind)
    | exact superpose eq128100 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq128100
       grind)
    | exact resolve eq12 eq128100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128100
  have eq130425 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq130420
  have eq130426 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq130425
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq130425
    | exact resolve eq130425 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130425
  have eq130956 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq130426
       grind)
    | exact superpose eq130426 eq16
    | exact resolve eq16 eq130426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130426
  have eq130970 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq130956
       have i₂ := eq127380
       grind)
    | exact superpose eq127380 eq130956
    | exact resolve eq130956 eq127380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130956
  have eq130971 : (σ x) = (σ (k y x)) ∨ x = y := by grind
  clear eq130970
  have eq131324 : (k y x) = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq130971
       grind)
    | exact superpose eq130971 eq10
    | exact resolve eq10 eq130971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130971
  have eq131498 : x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq131324
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq131324
    | exact resolve eq131324 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131324
  have eq131499 : x = (k y x) := by
    first
    | (have r₁ := eq131498
       have r₂ := eq127664
       grind)
    | exact resolve eq131498 eq127664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127664 eq131498
  have eq131795 : x = y ∨ x = y := by
    first
    | (have i₁ := eq127678
       have i₂ := eq131499
       grind)
    | exact superpose eq131499 eq127678
    | exact resolve eq127678 eq131499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127678
  have eq131909 : x = y := by grind
  clear eq131795
  have eq132197 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131909
       grind)
    | exact superpose eq131909 eq16
    | exact resolve eq16 eq131909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132198 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq131909
       grind)
    | exact superpose eq131909 eq115
    | exact resolve eq115 eq131909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq132230 : x = (M.op x x) := by
    first
    | (have i₁ := eq127380
       have i₂ := eq131909
       grind)
    | exact superpose eq131909 eq127380
    | exact resolve eq127380 eq131909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127380
  have eq132234 : x = (k x x) := by
    first
    | (have i₁ := eq131499
       have i₂ := eq131909
       grind)
    | exact superpose eq131909 eq131499
    | exact resolve eq131499 eq131909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131499 eq131909
  have eq132261 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq132198
  have eq132262 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq132261
       have i₂ := eq132230
       grind)
    | exact superpose eq132230 eq132261
    | exact resolve eq132261 eq132230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132261
  have eq132263 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq132197
       have i₂ := eq132230
       grind)
    | exact superpose eq132230 eq132197
    | exact resolve eq132197 eq132230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132197 eq132230
  have eq132264 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq132262
       have i₂ := eq132234
       grind)
    | exact superpose eq132234 eq132262
    | exact resolve eq132262 eq132234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132234 eq132262
  have eq132265 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq132264
  have eq132266 : False := by grind
  exact eq132266

/-- `Equation640`: `x = x ◇ (y ◇ ((y ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation640 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law640 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law640.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq104 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47 x y
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 x y
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq361 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq390 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq361
    | (have j0 := eq361 X0 X1
       grind)
    | exact resolve eq361 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq726 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq104
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq104
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq104
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq104
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq104 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq727 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq726
  have eq4850 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq727
       grind)
    | exact superpose eq727 eq16
    | exact resolve eq16 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4853 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq727
       grind)
    | exact superpose eq727 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq727
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq727
       grind)
    | exact resolve eq13 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq4860 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4853
  have eq4861 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4860
  have eq4869 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4861
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4861
    | exact resolve eq4861 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4861
  have eq7590 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq390 y x
       have i₂ := eq4869
       grind)
    | exact superpose eq4869 eq390
    | (have j0 := eq390 y x
       grind)
    | exact resolve eq390 eq4869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq7592 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq4869
       grind)
    | exact superpose eq4869 eq10
    | exact resolve eq10 eq4869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4869
  have eq7637 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq7590
  have eq7663 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq7592
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7592
    | exact resolve eq7592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7592
  have eq7664 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7637
       have r₂ := eq4850
       grind)
    | exact resolve eq7637 eq4850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4850 eq7637
  have eq7667 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq7663
       have r₂ := eq13 x y
       grind)
    | exact resolve eq7663 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7663
  have eq8021 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq109 x y
       have i₂ := eq7667
       grind)
    | exact superpose eq7667 eq109
    | (have j0 := eq109 x y
       grind)
    | exact resolve eq109 eq7667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq7667
  have eq8033 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8021
  have eq8034 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8033
  have eq8179 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq8034
       grind)
    | exact superpose eq8034 eq16
    | exact resolve eq16 eq8034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8034
  have eq8387 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8179
       have i₂ := eq7664
       grind)
    | exact superpose eq7664 eq8179
    | exact resolve eq8179 eq7664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7664 eq8179
  have eq8388 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8387
  have eq8389 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq8388
  have eq8572 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8389
       grind)
    | exact superpose eq8389 eq10
    | exact resolve eq10 eq8389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8389
  have eq8646 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8572
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8572
    | exact resolve eq8572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8572
  have eq8647 : x = y := by grind
  clear eq8646
  have eq8833 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8647
       grind)
    | exact superpose eq8647 eq16
    | exact resolve eq16 eq8647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8647
  have eq8834 : False := by grind
  exact eq8834

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_x_pxx_x_pxy_Equation643 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law643 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) ≠ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X1) ∨ (M.op X0 (M.op (M.op X0 X0) X0)) = (k (M.op X0 (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 (M.op (M.op X1 X1) X1)) X1
       have i₂ := eq9 (M.op X1 (M.op (M.op X1 X1) X1)) X1
       grind)
    | exact superpose eq9 eq12
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq39 (σ X0)
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq41
    | exact resolve eq41 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq41
  have eq76 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq143 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq9
    | exact resolve eq9 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (k (M.op X0 (M.op (M.op X0 X0) X0)) X1) ∨ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X1) = (k (M.op X0 (M.op (M.op X0 X0) X0)) X1) ∨ (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       have i₂ := eq78 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       grind)
    | exact superpose eq78 eq9
    | (have j1 := eq78 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       grind)
    | exact resolve eq9 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq239 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq232 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq232 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq232 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq232 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq247 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X1) = (k (M.op X0 (M.op (M.op X0 X0) X0)) X1) ∨ (M.op X0 (M.op (M.op X0 X0) X0)) = (k (M.op X0 (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq219 X0 X1
       have j1 := eq37 X0 X1
       grind)
    | (have r₁ := eq219 X0 X1
       have r₂ := eq37 X0 X1
       grind)
    | exact resolve eq219 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq219
  have eq309 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq239 (σ X0) (σ X1)
       grind)
    | exact superpose eq239 eq15
    | (have j1 := eq239 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq239 X0 (τ X1)
       grind)
    | exact superpose eq239 eq18
    | (have j1 := eq239 X0 (τ X1)
       grind)
    | exact resolve eq18 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq336 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq143 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq143
    | exact resolve eq143 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq383 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X1
       have i₂ := eq46 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq46 eq336
    | exact resolve eq336 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq391 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq383 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq383
    | exact resolve eq383 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq393 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq391 X0 X1
       have i₂ := eq46 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq46 eq391
    | exact resolve eq391 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq395 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq393 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq393
    | exact resolve eq393 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq13179 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq315 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq315
    | exact resolve eq315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq13290 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13179 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq13179
    | (have j0 := eq13179 X0 X1
       grind)
    | exact resolve eq13179 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13179
  have eq18476 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq309 x y
       grind)
    | exact superpose eq309 eq16
    | (have j1 := eq309 x y
       grind)
    | exact resolve eq16 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18583 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq309 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq27197 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18476
       have i₂ := eq13290 y x
       grind)
    | exact superpose eq13290 eq18476
    | (have j1 := eq13290 (σ y) (σ x)
       grind)
    | (have r₁ := eq18476
       have r₂ := eq13290 y x
       grind)
    | exact resolve eq18476 eq13290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27198 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27197
  have eq27501 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27198
       grind)
    | exact superpose eq27198 eq16
    | exact resolve eq16 eq27198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27504 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq27198
       grind)
    | exact superpose eq27198 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq27198
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq27198
       grind)
    | exact resolve eq13 eq27198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27198
  have eq27509 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27504
  have eq27512 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27509
       have i₂ := eq46 x
       grind)
    | exact superpose eq46 eq27509
    | exact resolve eq27509 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq27509
  have eq27518 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27512
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq27512
    | exact resolve eq27512 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27512
  have eq119690 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13290 y x
       have i₂ := eq27518
       grind)
    | exact superpose eq27518 eq13290
    | (have j0 := eq13290 y x
       grind)
    | exact resolve eq13290 eq27518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13290 eq27518
  have eq119810 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq119690
  have eq119848 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq119810
       have r₂ := eq27501
       grind)
    | exact resolve eq119810 eq27501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119810
  have eq120861 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq119848
       grind)
    | exact superpose eq119848 eq10
    | exact resolve eq10 eq119848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119848
  have eq120995 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120861
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq120861
    | exact resolve eq120861 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120861
  have eq122131 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq120995
       grind)
    | exact superpose eq120995 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq120995
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq120995
       grind)
    | exact resolve eq13 eq120995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122135 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by grind
  clear eq122131
  have eq122136 : x = (k x y) ∨ x = (M.op x x) := by grind
  clear eq122135
  have eq123185 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18583 x y
       have i₂ := eq122136
       grind)
    | exact superpose eq122136 eq18583
    | (have j0 := eq18583 x y
       grind)
    | exact resolve eq18583 eq122136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122136
  have eq123196 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq123185
  have eq125702 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq123196
       grind)
    | exact superpose eq123196 eq16
    | exact resolve eq16 eq123196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123196
  have eq126638 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq125702
       have i₂ := eq120995
       grind)
    | exact superpose eq120995 eq125702
    | exact resolve eq125702 eq120995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120995 eq125702
  have eq126639 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by grind
  clear eq126638
  have eq126640 : x = (M.op x x) := by grind
  clear eq126639
  have eq127464 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq126640
       grind)
    | exact superpose eq126640 eq9
    | exact resolve eq9 eq126640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127490 : ∀ X0 : G, (M.op (M.op x (M.op x x)) X0) = (k (M.op x (M.op x x)) X0) ∨ (M.op x (M.op x x)) = (k (M.op x (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq247 x x
       have i₂ := eq126640
       grind)
    | exact superpose eq126640 eq247
    | exact resolve eq247 eq126640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq127496 : ∀ X0 : G, (M.op X0 (σ (M.op x (M.op x x)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq395 x X0
       have i₂ := eq126640
       grind)
    | exact superpose eq126640 eq395
    | exact resolve eq395 eq126640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq127736 : ∀ X0 : G, (M.op X0 (σ (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq127496 X0
       have i₂ := eq126640
       grind)
    | exact superpose eq126640 eq127496
    | exact resolve eq127496 eq126640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127496
  have eq127741 : ∀ X0 : G, (k (M.op x x) X0) = (M.op (M.op x x) X0) ∨ (M.op x (M.op x x)) = (k (M.op x (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq127490 X0
       have i₂ := eq126640
       grind)
    | exact superpose eq126640 eq127490
    | (have j0 := eq127490 X0
       grind)
    | exact resolve eq127490 eq126640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127490
  have eq127753 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq127464 X0
       have i₂ := eq126640
       grind)
    | exact superpose eq126640 eq127464
    | exact resolve eq127464 eq126640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127464
  have eq127858 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq127736 X0
       have i₂ := eq126640
       grind)
    | exact superpose eq126640 eq127736
    | exact resolve eq127736 eq126640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127736
  have eq127863 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ (M.op x (M.op x x)) = (k (M.op x (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq127741 X0
       have i₂ := eq126640
       grind)
    | exact superpose eq126640 eq127741
    | (have j0 := eq127741 X0
       grind)
    | exact resolve eq127741 eq126640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127741
  have eq127875 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq127753 X0
       have i₂ := eq126640
       grind)
    | exact superpose eq126640 eq127753
    | exact resolve eq127753 eq126640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127753
  have eq127928 : ∀ X0 : G, (M.op x x) = (k (M.op x x) X0) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq127863 X0
       have i₂ := eq126640
       grind)
    | exact superpose eq126640 eq127863
    | (have j0 := eq127863 X0
       grind)
    | exact resolve eq127863 eq126640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126640 eq127863
  have eq127978 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq127928 X0
       have i₂ := eq127875 x
       grind)
    | exact superpose eq127875 eq127928
    | (have j0 := eq127928 X0
       grind)
    | exact resolve eq127928 eq127875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127875 eq127928
  have eq194702 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq18476
       have i₂ := eq127978 y
       grind)
    | exact superpose eq127978 eq18476
    | (have j1 := eq127978 y
       grind)
    | exact resolve eq18476 eq127978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18476 eq127978
  have eq194882 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq194702
  have eq206028 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq194882
       grind)
    | exact superpose eq194882 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq194882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194882
  have eq206037 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq206028
       have r₂ := eq127858 (σ x)
       grind)
    | exact resolve eq206028 eq127858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206028
  have eq206044 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq206037
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq206037
    | exact resolve eq206037 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206037
  have eq206046 : (σ x) = (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq206044
       have i₂ := eq127858 (σ x)
       grind)
    | exact superpose eq127858 eq206044
    | exact resolve eq206044 eq127858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127858 eq206044
  have eq210159 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq206046
       have i₂ := eq239 x y
       grind)
    | exact superpose eq239 eq206046
    | (have j1 := eq239 x y
       grind)
    | exact resolve eq206046 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq210177 : (k x y) = (τ (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq206046
       grind)
    | exact superpose eq206046 eq10
    | exact resolve eq10 eq206046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206046
  have eq210299 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq210159
  have eq210357 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq210177
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq210177
    | exact resolve eq210177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210177
  have eq210358 : x = (k x y) := by grind
  clear eq210357
  have eq210371 : x = (M.op x y) := by
    first
    | (have r₁ := eq210299
       have r₂ := eq27501
       grind)
    | exact resolve eq210299 eq27501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27501 eq210299
  have eq212231 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18583 x y
       have i₂ := eq210358
       grind)
    | exact superpose eq210358 eq18583
    | (have j0 := eq18583 x y
       grind)
    | exact resolve eq18583 eq210358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18583 eq210358
  have eq212242 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq212231
  have eq218038 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq212242
       grind)
    | exact superpose eq212242 eq16
    | exact resolve eq16 eq212242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212242
  have eq218052 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq218038
       have i₂ := eq210371
       grind)
    | exact superpose eq210371 eq218038
    | exact resolve eq218038 eq210371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210371 eq218038
  have eq218053 : False := by grind
  exact eq218053

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_y_pxx_y_pxy_Equation643 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law643 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq39 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq39 (σ X0)
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq41
    | exact resolve eq41 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq41
  have eq76 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq112 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq12
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq166 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq163 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq163 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq163 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq163 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq163 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq298 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq166 (σ X0) (σ X1)
       grind)
    | exact superpose eq166 eq15
    | (have j1 := eq166 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq166 (τ X0) X1
       grind)
    | exact superpose eq166 eq17
    | (have j1 := eq166 (τ X0) X1
       grind)
    | exact resolve eq17 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq166
  have eq5750 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq300 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq300
    | exact resolve eq300 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq5879 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5750 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5750
    | (have j0 := eq5750 X0 X1
       grind)
    | exact resolve eq5750 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5750
  have eq17976 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq298 x y
       grind)
    | exact superpose eq298 eq16
    | (have j1 := eq298 x y
       grind)
    | exact resolve eq16 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18070 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq19549 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17976
       have i₂ := eq5879 x y
       grind)
    | exact superpose eq5879 eq17976
    | (have j1 := eq5879 (σ x) (σ y)
       grind)
    | (have r₁ := eq17976
       have r₂ := eq5879 x y
       grind)
    | exact resolve eq17976 eq5879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17976
  have eq19550 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19549
  have eq19806 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19550
       grind)
    | exact superpose eq19550 eq16
    | exact resolve eq16 eq19550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19809 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq19550
       grind)
    | exact superpose eq19550 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19550
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19550
       grind)
    | exact resolve eq13 eq19550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19813 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19809
  have eq19814 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19813
       have i₂ := eq46 x
       grind)
    | exact superpose eq46 eq19813
    | exact resolve eq19813 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq19813
  have eq19819 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19814
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19814
    | exact resolve eq19814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19814
  have eq43025 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5879 x y
       have i₂ := eq19819
       grind)
    | exact superpose eq19819 eq5879
    | (have j0 := eq5879 x y
       grind)
    | exact resolve eq5879 eq19819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19819
  have eq43108 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq43025
  have eq43145 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq43108
       have r₂ := eq19806
       grind)
    | exact resolve eq43108 eq19806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43108
  have eq43195 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq43145
       grind)
    | exact superpose eq43145 eq10
    | exact resolve eq10 eq43145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43145
  have eq43288 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq43195
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq43195
    | exact resolve eq43195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43195
  have eq43635 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq43288
       grind)
    | exact superpose eq43288 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq43288
       grind)
    | exact resolve eq13 eq43288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43638 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by grind
  clear eq43635
  have eq43639 : y = (k x y) ∨ y = (M.op x x) := by grind
  clear eq43638
  have eq44023 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18070 x y
       have i₂ := eq43639
       grind)
    | exact superpose eq43639 eq18070
    | (have j0 := eq18070 x y
       grind)
    | exact resolve eq18070 eq43639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43639
  have eq44034 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq44023
  have eq45683 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44034
       grind)
    | exact superpose eq44034 eq16
    | exact resolve eq16 eq44034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44034
  have eq46669 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45683
       have i₂ := eq43288
       grind)
    | exact superpose eq43288 eq45683
    | exact resolve eq45683 eq43288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43288 eq45683
  have eq46670 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq46669
  have eq46671 : y = (M.op x x) := by grind
  clear eq46670
  have eq47467 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq46671
       grind)
    | exact superpose eq46671 eq12
    | exact resolve eq12 eq46671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47477 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) ∨ (σ y) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq112 x x
       have i₂ := eq46671
       grind)
    | exact superpose eq46671 eq112
    | exact resolve eq112 eq46671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq46671
  have eq70727 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq47477 (σ y)
       have i₂ := eq19550
       grind)
    | exact superpose eq19550 eq47477
    | (have j0 := eq47477 (σ y)
       grind)
    | (have r₁ := eq47477 (σ y)
       have r₂ := eq19550
       grind)
    | exact resolve eq47477 eq19550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19550 eq47477
  have eq70795 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq70727
  have eq70825 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70795
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq70795
    | exact resolve eq70795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70795
  have eq70905 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5879 x y
       have i₂ := eq70825
       grind)
    | exact superpose eq70825 eq5879
    | (have j0 := eq5879 x y
       grind)
    | exact resolve eq5879 eq70825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5879
  have eq70909 : (k x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq70825
       grind)
    | exact superpose eq70825 eq10
    | exact resolve eq10 eq70825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70825
  have eq71001 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq70905
  have eq71036 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70909
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq70909
    | exact resolve eq70909 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70909
  have eq71037 : y = (M.op x y) := by
    first
    | (have r₁ := eq71001
       have r₂ := eq19806
       grind)
    | exact resolve eq71001 eq19806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19806 eq71001
  have eq71046 : y = (k x y) := by
    first
    | (have j1 := eq47467 y
       grind)
    | (have r₁ := eq71036
       have r₂ := eq47467 y
       grind)
    | exact resolve eq71036 eq47467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47467 eq71036
  have eq72287 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18070 x y
       have i₂ := eq71046
       grind)
    | exact superpose eq71046 eq18070
    | (have j0 := eq18070 x y
       grind)
    | exact resolve eq18070 eq71046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18070 eq71046
  have eq72298 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq72287
  have eq74549 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72298
       grind)
    | exact superpose eq72298 eq16
    | exact resolve eq16 eq72298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72298
  have eq74564 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq74549
       have i₂ := eq71037
       grind)
    | exact superpose eq71037 eq74549
    | exact resolve eq74549 eq71037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71037 eq74549
  have eq74565 : False := by grind
  exact eq74565

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_pxx_pxy_Equation643 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law643 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = M.op a a :=
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
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq40 (σ X0)
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq42
    | exact resolve eq42 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq42
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq106 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq103 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq103 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq103 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq103 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq200 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq106 (σ X0) (σ X1)
       grind)
    | exact superpose eq106 eq15
    | (have j1 := eq106 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq106 (τ X0) X1
       grind)
    | exact superpose eq106 eq18
    | (have j1 := eq106 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq106
  have eq1033 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq202 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq202
    | exact resolve eq202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq1082 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1033 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1033
    | (have j0 := eq1033 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq1033 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq4054 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq200 x y
       grind)
    | exact superpose eq200 eq16
    | (have j1 := eq200 x y
       grind)
    | exact resolve eq16 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq4429 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4054
       have i₂ := eq1082 x y
       grind)
    | exact superpose eq1082 eq4054
    | (have j1 := eq1082 (σ x) (σ y)
       grind)
    | (have r₁ := eq4054
       have r₂ := eq1082 x y
       grind)
    | (have r₁ := eq4054
       have r₂ := eq1082 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4054
       have r₂ := eq1082 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4054 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082 eq4054
  have eq4430 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq4429
  have eq4739 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4430
       grind)
    | exact superpose eq4430 eq10
    | exact resolve eq10 eq4430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4430
  have eq4786 : x = y ∨ x = y := by
    first
    | (have i₁ := eq4739
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4739
    | exact resolve eq4739 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4739
  have eq4787 : x = y := by grind
  clear eq4786
  have eq5069 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4787
       grind)
    | exact superpose eq4787 eq16
    | exact resolve eq16 eq4787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4787
  have eq5070 : False := by grind
  exact eq5070

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_Equation643 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law643 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
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
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq40 (σ X0)
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq44
    | exact resolve eq44 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq44
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq67 (σ X0) (σ X1)
       grind)
    | exact superpose eq67 eq15
    | (have j1 := eq67 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq67 (τ X0) X1
       grind)
    | exact superpose eq67 eq18
    | (have j1 := eq67 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq67
  have eq193 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq217 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq193 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq193
    | (have j0 := eq193 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq193 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq593 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72 x y
       grind)
    | exact superpose eq72 eq16
    | (have j1 := eq72 x y
       grind)
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq1062 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq593
       have i₂ := eq217 x y
       grind)
    | exact superpose eq217 eq593
    | (have j1 := eq217 (σ x) (σ y)
       grind)
    | (have r₁ := eq593
       have r₂ := eq217 x y
       grind)
    | (have r₁ := eq593
       have r₂ := eq217 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq593
       have r₂ := eq217 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq593 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq593
  have eq1063 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1062
  have eq1251 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1063
       grind)
    | exact superpose eq1063 eq10
    | exact resolve eq10 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1288 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1251
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1251
    | exact resolve eq1251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1289 : x = y := by grind
  clear eq1288
  have eq1494 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1289
       grind)
    | exact superpose eq1289 eq16
    | exact resolve eq16 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq1495 : False := by grind
  exact eq1495

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation643 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law643 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq40 (σ X0)
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq43
    | exact resolve eq43 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq43
  have eq57 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X2 X1) = (M.op X2 X1) ∨ X1 = X2 ∨ (k X2 X0) = (M.op X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq14 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X2 X1
       have j1 := eq14 X2 X1
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X2 X1) = (M.op X2 X1) ∨ (k X2 X0) = (M.op X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X1) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (k X2 X1) = (M.op X2 X1) ∨ (k X2 X0) = (M.op X2 X0) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq57 X1 X1 X2
       have j1 := eq66 X1 X1 X2
       grind)
    | (have r₁ := eq57 X0 X1 X2
       have r₂ := eq66 X0 X1 X2
       grind)
    | (have r₁ := eq57 X1 X0 X2
       have r₂ := eq66 X0 X1 X2
       grind)
    | (have r₁ := eq57 X0 (M.op X1 X1) (M.op X0 X0)
       have r₂ := eq66 X0 X1 X2
       grind)
    | exact resolve eq57 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq66
  have eq145 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq74 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq146 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq147 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq146 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq241 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq147 (σ X0) (σ X1)
       grind)
    | exact superpose eq147 eq15
    | (have j1 := eq147 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq147 (τ X0) X1
       grind)
    | exact superpose eq147 eq18
    | (have j1 := eq147 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq147
  have eq816 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq243 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq243
    | exact resolve eq243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq852 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq816 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq816
    | (have j0 := eq816 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq816 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq3380 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq241 x y
       grind)
    | exact superpose eq241 eq16
    | (have j1 := eq241 x y
       grind)
    | exact resolve eq16 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq3487 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3380
       have i₂ := eq852 x y
       grind)
    | exact superpose eq852 eq3380
    | (have j1 := eq852 (σ x) (σ y)
       grind)
    | (have r₁ := eq3380
       have r₂ := eq852 x y
       grind)
    | (have r₁ := eq3380
       have r₂ := eq852 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3380
       have r₂ := eq852 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3380 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852 eq3380
  have eq3488 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3487
  have eq3578 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3488
       grind)
    | exact superpose eq3488 eq10
    | exact resolve eq10 eq3488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3488
  have eq3620 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3578
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3578
    | exact resolve eq3578 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3578
  have eq3621 : x = y := by grind
  clear eq3620
  have eq3704 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3621
       grind)
    | exact superpose eq3621 eq16
    | exact resolve eq16 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621
  have eq3705 : False := by grind
  exact eq3705

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_y_pxy_y_pyx_Equation643 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law643 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) ≠ (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (k (M.op X0 (M.op (M.op X0 X0) X0)) X1) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op (M.op X1 X1) X1)) X1
       have r₂ := eq9 (M.op X1 (M.op (M.op X1 X1) X1)) X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k (M.op X0 (M.op (M.op X0 X0) X0)) X1) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq62 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq65 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq67 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X2 := by
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
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq67 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq137 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq246 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq62 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq248 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq246 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq300 : ∀ X0 : G, (σ (M.op X0 (M.op (M.op X0 X0) X0))) ≠ (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))) ∨ (σ (M.op X0 (M.op (M.op X0 X0) X0))) = (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq248 (M.op X0 (M.op (M.op X0 X0) X0))
       have i₂ := eq38 X0 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq38 eq248
    | (have j0 := eq248 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact resolve eq248 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq248
  have eq309 : ∀ X0 : G, (σ (M.op X0 (M.op (M.op X0 X0) X0))) ≠ (σ (M.op X0 (M.op (M.op X0 X0) X0))) ∨ (σ (M.op X0 (M.op (M.op X0 X0) X0))) = (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq300 X0
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq300
    | (have j0 := eq300 X0
       grind)
    | exact resolve eq300 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq310 : ∀ X0 : G, (σ (M.op X0 (M.op (M.op X0 X0) X0))) = (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have j0 := eq309 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq353 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq137 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq354 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq353 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq353 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq353 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq368 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq354 (σ X0)
       grind)
    | exact superpose eq354 eq15
    | exact resolve eq15 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0 X0
       have i₂ := eq354 (τ X0)
       grind)
    | exact superpose eq354 eq39
    | exact resolve eq39 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq372
    | exact resolve eq372 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq379 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq368 X0
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq368
    | exact resolve eq368 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq368
  have eq432 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65
    | (have j0 := eq65 X0 X1
       grind)
    | exact resolve eq65 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq474 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq432 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq432
    | (have j0 := eq432 X1 X1
       grind)
    | exact resolve eq432 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq489 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq379 X0
       grind)
    | exact superpose eq379 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq379 X0
       grind)
    | exact superpose eq379 eq9
    | exact resolve eq9 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq247 (τ X1) (τ X0)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq247
    | (have j0 := eq247 (τ X0) (τ X0)
       grind)
    | exact resolve eq247 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq247
  have eq989 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq979 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq979
    | (have j0 := eq979 X0 X0
       grind)
    | exact resolve eq979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1000 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq989
    | (have j0 := eq989 X0 X0
       grind)
    | exact resolve eq989 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq1006 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1000 X0 X1
       have i₂ := eq379 (τ X0)
       grind)
    | exact superpose eq379 eq1000
    | (have j0 := eq1000 X0 X1
       grind)
    | exact resolve eq1000 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1008 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X0 X0))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1006 X0 X1
       have i₂ := eq375 X0
       grind)
    | exact superpose eq375 eq1006
    | (have j0 := eq1006 X0 X1
       grind)
    | exact resolve eq1006 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq1006
  have eq1010 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1008 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1008
    | (have j0 := eq1008 X0 X1
       grind)
    | exact resolve eq1008 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1011 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1010 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1010
    | (have j0 := eq1010 X0 X1
       grind)
    | exact resolve eq1010 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1012 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1011 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1011
    | (have j0 := eq1011 X0 X1
       grind)
    | exact resolve eq1011 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1013 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1012 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1012
    | (have j0 := eq1012 X0 X1
       grind)
    | exact resolve eq1012 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1014 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq491 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq491
    | exact resolve eq491 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq1085 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1014 X0 X1
       have i₂ := eq310 X0
       grind)
    | exact superpose eq310 eq1014
    | exact resolve eq1014 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1108 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1085 X0 X1
       have i₂ := eq310 X0
       grind)
    | exact superpose eq310 eq1085
    | exact resolve eq1085 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310 eq1085
  have eq129731 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq489 X0 X1
       grind)
    | exact superpose eq489 eq10
    | (have j1 := eq489 X0 X1
       grind)
    | exact resolve eq10 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq129938 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq129731 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq129731
    | (have j0 := eq129731 X0 X1
       grind)
    | exact resolve eq129731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129731
  have eq131043 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq129938 X1 (σ X0)
       grind)
    | exact superpose eq129938 eq15
    | (have j1 := eq129938 X1 (σ X0)
       grind)
    | exact resolve eq15 eq129938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129938
  have eq379938 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131043 x y
       grind)
    | exact superpose eq131043 eq16
    | (have j1 := eq131043 x y
       grind)
    | exact resolve eq16 eq131043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379988 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq131043 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131043
  have eq387976 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq379938
       have i₂ := eq474 x y
       grind)
    | exact superpose eq474 eq379938
    | (have j1 := eq474 y y
       grind)
    | (have r₁ := eq379938
       have r₂ := eq474 x y
       grind)
    | exact resolve eq379938 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq379938
  have eq387977 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq387976
  have eq387978 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq387977
  have eq388517 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq387978
       grind)
    | exact superpose eq387978 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq387978
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq387978
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq387978
       grind)
    | exact resolve eq13 eq387978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387978
  have eq388518 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq388517
  have eq388520 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq388518
       have i₂ := eq379 y
       grind)
    | exact superpose eq379 eq388518
    | exact resolve eq388518 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq388518
  have eq388522 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq388520
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq388520
    | exact resolve eq388520 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388520
  have eq741428 : (k y x) = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq388522
       grind)
    | exact superpose eq388522 eq10
    | exact resolve eq10 eq388522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388522
  have eq741437 : x = (k y x) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq741428
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq741428
    | exact resolve eq741428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741428
  have eq741438 : (σ y) = (σ (M.op y y)) ∨ x = (k y x) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq741437
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq741437
       have r₂ := eq13 y x
       grind)
    | exact resolve eq741437 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741437
  have eq745207 : (M.op y y) = (τ (σ y)) ∨ x = (k y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq741438
       grind)
    | exact superpose eq741438 eq10
    | exact resolve eq10 eq741438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741438
  have eq745258 : y = (M.op y y) ∨ x = (k y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq745207
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq745207
    | exact resolve eq745207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745207
  have eq745259 : x = (k y x) ∨ y = (M.op y y) := by grind
  clear eq745258
  have eq747624 : x ≠ x ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1013 y x
       have i₂ := eq745259
       grind)
    | exact superpose eq745259 eq1013
    | (have j0 := eq1013 y y
       grind)
    | (have r₁ := eq1013 y x
       have r₂ := eq745259
       grind)
    | exact resolve eq1013 eq745259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq747665 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq379988 x y
       have i₂ := eq745259
       grind)
    | exact superpose eq745259 eq379988
    | (have j0 := eq379988 x y
       grind)
    | exact resolve eq379988 eq745259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379988 eq745259
  have eq747675 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq747665
  have eq747676 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq747675
  have eq747703 : x ≠ x ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq747624
  have eq747704 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq747703
  have eq750167 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq747704
       grind)
    | exact superpose eq747704 eq9
    | exact resolve eq9 eq747704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq759495 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq747676
       grind)
    | exact superpose eq747676 eq16
    | exact resolve eq16 eq747676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747676
  have eq766295 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq750167 X0
       have i₂ := eq747704
       grind)
    | exact superpose eq747704 eq750167
    | exact resolve eq750167 eq747704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747704
  have eq766321 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq766295 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766295
  have eq769132 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq750167 X0
       have i₂ := eq766321 y
       grind)
    | exact superpose eq766321 eq750167
    | exact resolve eq750167 eq766321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750167 eq766321
  have eq769133 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq769132 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769132
  have eq771529 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq769133 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769133
  have eq771530 : x = (M.op x y) := by grind
  clear eq771529
  have eq774334 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq759495
       have i₂ := eq771530
       grind)
    | exact superpose eq771530 eq759495
    | exact resolve eq759495 eq771530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759495 eq771530
  have eq774337 : y = (M.op y y) := by grind
  clear eq774334
  have eq777501 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq774337
       grind)
    | exact superpose eq774337 eq9
    | exact resolve eq9 eq774337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777554 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1108 y X0
       have i₂ := eq774337
       grind)
    | exact superpose eq774337 eq1108
    | exact resolve eq1108 eq774337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq777876 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq777554 X0
       have i₂ := eq774337
       grind)
    | exact superpose eq774337 eq777554
    | exact resolve eq777554 eq774337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777554
  have eq777914 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq777501 X0
       have i₂ := eq774337
       grind)
    | exact superpose eq774337 eq777501
    | exact resolve eq777501 eq774337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777501
  have eq778057 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq777876 X0
       have i₂ := eq774337
       grind)
    | exact superpose eq774337 eq777876
    | exact resolve eq777876 eq774337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777876
  have eq778093 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq777914 X0
       have i₂ := eq774337
       grind)
    | exact superpose eq774337 eq777914
    | exact resolve eq777914 eq774337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774337 eq777914
  have eq784874 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq778057 (σ x)
       grind)
    | exact superpose eq778057 eq16
    | exact resolve eq16 eq778057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778057
  have eq784935 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq784874
       have i₂ := eq778093 x
       grind)
    | exact superpose eq778093 eq784874
    | exact resolve eq784874 eq778093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778093 eq784874
  have eq784936 : False := by grind
  exact eq784936

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pxy_Equation643 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law643 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) ≠ (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 (M.op (M.op X0 X0) X0))
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X1 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op (M.op X1 X1) X1))
       have r₂ := eq9 (M.op X1 (M.op (M.op X1 X1) X1)) X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 (M.op (M.op X0 X0) X0))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq78 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq73 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq73 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq73 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq109 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq78 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq109 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq110 (σ X0)
       grind)
    | exact superpose eq110 eq15
    | exact resolve eq15 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq114
    | exact resolve eq114 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq114
  have eq168 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq9
    | exact resolve eq9 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq168 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq168 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq205 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = (M.op X0 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78 X0 (M.op X1 (M.op (M.op X1 X1) X1)) X2
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq78
    | (have j0 := eq78 X2 X0 X2
       have j1 := eq48 X0 X0
       grind)
    | exact resolve eq78 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq78
  have eq210 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq205 X0 x X2
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq205
    | (have j0 := eq205 X0 x X2
       grind)
    | exact resolve eq205 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq211 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have j0 := eq210 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq292 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq211 X1 (τ X0)
       grind)
    | exact superpose eq211 eq17
    | (have j1 := eq211 X1 x
       grind)
    | exact resolve eq17 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq211
  have eq347 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq172 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq172
    | exact resolve eq172 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq389 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq347 X0 X1
       have i₂ := eq125 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq125 eq347
    | exact resolve eq347 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq400 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq389 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq389
    | exact resolve eq389 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq402 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq400 X0 X1
       have i₂ := eq125 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq125 eq400
    | exact resolve eq400 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq400
  have eq404 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq402
    | exact resolve eq402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq3590 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq292 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq292
    | (have j0 := eq292 X0 X1
       grind)
    | exact resolve eq292 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq3714 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3590 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3590
    | (have j0 := eq3590 X0 X1
       grind)
    | exact resolve eq3590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3590
  have eq10525 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq174 X0 X1
       grind)
    | exact superpose eq174 eq10
    | (have j1 := eq174 X0 X1
       grind)
    | exact resolve eq10 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq10615 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10525 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10525
    | (have j0 := eq10525 X0 X1
       grind)
    | exact resolve eq10525 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10525
  have eq11199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq10615 X1 (σ X0)
       grind)
    | exact superpose eq10615 eq15
    | (have j1 := eq10615 X1 X1
       grind)
    | exact resolve eq15 eq10615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10615
  have eq13279 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11199 x y
       grind)
    | exact superpose eq11199 eq16
    | (have j1 := eq11199 x y
       grind)
    | exact resolve eq16 eq11199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11199
  have eq13487 : y = (M.op y y) := by
    first
    | (have j1 := eq3714 x y
       grind)
    | (have r₁ := eq13279
       have r₂ := eq3714 x y
       grind)
    | exact resolve eq13279 eq3714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3714 eq13279
  have eq13956 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq13487
       grind)
    | exact superpose eq13487 eq9
    | exact resolve eq9 eq13487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13978 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq404 y X0
       have i₂ := eq13487
       grind)
    | exact superpose eq13487 eq404
    | exact resolve eq404 eq13487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq14011 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq13978 X0
       have i₂ := eq13487
       grind)
    | exact superpose eq13487 eq13978
    | exact resolve eq13978 eq13487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13978
  have eq14024 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13956 X0
       have i₂ := eq13487
       grind)
    | exact superpose eq13487 eq13956
    | exact resolve eq13956 eq13487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13956
  have eq14035 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14011 X0
       have i₂ := eq13487
       grind)
    | exact superpose eq13487 eq14011
    | exact resolve eq14011 eq13487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14011
  have eq14046 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq14024 X0
       have i₂ := eq13487
       grind)
    | exact superpose eq13487 eq14024
    | exact resolve eq14024 eq13487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13487 eq14024
  have eq16064 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14035 (σ x)
       grind)
    | exact superpose eq14035 eq16
    | exact resolve eq16 eq14035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14035
  have eq16095 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq16064
       have i₂ := eq14046 x
       grind)
    | exact superpose eq14046 eq16064
    | exact resolve eq16064 eq14046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14046 eq16064
  have eq16096 : False := by grind
  exact eq16096

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pyx_Equation643 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law643 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) ≠ (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 (M.op (M.op X0 X0) X0))
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X1 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op (M.op X1 X1) X1))
       have r₂ := eq9 (M.op X1 (M.op (M.op X1 X1) X1)) X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 (M.op (M.op X0 X0) X0))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) (τ X1)
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq75 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq97 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X1) X1))) ≠ X0 ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq48 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq12 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X1) X1))) ≠ X0 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq97 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq97 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq97 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq204 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X2) = (k (τ X0) X2) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq73 (τ X0) X2 X1
       grind)
    | exact superpose eq73 eq18
    | (have j1 := eq73 (τ X0) X2 X1
       grind)
    | exact resolve eq18 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq213 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq73 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq214 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq213 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq220 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq214 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq214 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq214 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq228 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq220 (σ X0)
       grind)
    | exact superpose eq220 eq15
    | exact resolve eq15 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0 X0
       have i₂ := eq220 (τ X0)
       grind)
    | exact superpose eq220 eq39
    | exact resolve eq39 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq230 X0
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq230
    | exact resolve eq230 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq235 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq228 X0
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq228
    | exact resolve eq228 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq296 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) X2) = (M.op (σ X1) X2) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq75 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq75 eq15
    | (have j1 := eq75 (σ X1) X2 (σ X0)
       grind)
    | exact resolve eq15 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq308 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) X2) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq296 X0 X1 X2
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq296
    | (have j0 := eq296 X0 X1 X2
       grind)
    | exact resolve eq296 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq326 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq9
    | exact resolve eq9 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq9
    | exact resolve eq9 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq326 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq326
    | exact resolve eq326 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq583 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq235 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq235 eq532
    | exact resolve eq532 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq593 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq583 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq583
    | exact resolve eq583 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq595 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq593 X0 X1
       have i₂ := eq235 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq235 eq593
    | exact resolve eq593 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq597 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq595 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq595
    | exact resolve eq595 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq1269 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (τ (M.op X0 (M.op (M.op X0 X0) X0))) (τ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq429 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq429
    | exact resolve eq429 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq1353 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op X0 (M.op (M.op X0 X0) X0))) (τ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1269 X0 X1
       have i₂ := eq233 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq233 eq1269
    | exact resolve eq1269 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269
  have eq1374 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op X0 (M.op (M.op X0 X0) X0))) (τ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1353 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq1353
    | exact resolve eq1353 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq1382 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1374 X0 X1
       have i₂ := eq233 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq233 eq1374
    | exact resolve eq1374 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq1389 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1382 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq1382
    | exact resolve eq1382 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq6103 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq6332 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6103 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6103
    | (have j0 := eq6103 X0 X0
       grind)
    | exact resolve eq6103 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6103
  have eq11604 : ∀ X0 X1 X2 : G, (σ (k (τ X0) (M.op X1 (M.op (M.op X1 X1) X1)))) = (k (σ (τ X0)) X0) ∨ (M.op (τ X0) X2) = (k (τ X0) X2) ∨ (τ X0) = (k (τ X0) (M.op X1 (M.op (M.op X1 X1) X1))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq204 X0 (τ X0) X2
       have i₂ := eq48 X0 (τ X0)
       grind)
    | exact superpose eq48 eq204
    | (have j0 := eq204 X0 (τ X0) X2
       have j1 := eq48 X0 (τ X0)
       grind)
    | exact resolve eq204 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq11854 : ∀ X0 X1 X2 : G, (σ (k (τ X0) (M.op X1 (M.op (M.op X1 X1) X1)))) = (k (σ (τ X0)) X0) ∨ (M.op (τ X0) X2) = (k (τ X0) X2) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq11604 X0 X1 X2
       have j1 := eq111 (τ X0) X1 X2
       grind)
    | (have r₁ := eq11604 X0 X1 X2
       have r₂ := eq111 (τ X0) X1 X2
       grind)
    | exact resolve eq11604 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq11604
  have eq11875 : ∀ X0 X1 X2 : G, (σ (k (τ X0) (M.op X1 (M.op (M.op X1 X1) X1)))) = (k (σ (τ X0)) X0) ∨ (M.op (τ X0) X2) = (k (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq11854 X0 X1 X2
       have j1 := eq12 (τ X0) X2
       grind)
    | (have r₁ := eq11854 X0 X1 X2
       have r₂ := eq12 (τ X0) X1
       grind)
    | exact resolve eq11854 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11854
  have eq11889 : ∀ X0 X1 X2 : G, (k X0 X0) = (σ (k (τ X0) (M.op X1 (M.op (M.op X1 X1) X1)))) ∨ (M.op (τ X0) X2) = (k (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11875 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11875
    | (have j0 := eq11875 X0 X1 X2
       grind)
    | exact resolve eq11875 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11875
  have eq11894 : ∀ X0 X1 X2 : G, (k X0 X0) = (k X0 (σ (M.op X1 (M.op (M.op X1 X1) X1)))) ∨ (M.op (τ X0) X2) = (k (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11889 X0 X1 X2
       have i₂ := eq17 X0 (M.op X1 (M.op (M.op X1 X1) X1))
       grind)
    | exact superpose eq17 eq11889
    | (have j0 := eq11889 X0 X1 X2
       grind)
    | exact resolve eq11889 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq11889
  have eq11897 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (σ (M.op X1 (M.op (M.op X1 X1) X1)))) ∨ (M.op (τ X0) X2) = (k (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11894 X0 X1 X2
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq11894
    | (have j0 := eq11894 X0 X1 X2
       grind)
    | exact resolve eq11894 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq11894
  have eq23769 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) X2) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq308 X0 X1 X2
       grind)
    | exact superpose eq308 eq10
    | (have j1 := eq308 X0 X1 X2
       grind)
    | exact resolve eq10 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq24092 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) X2) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23769 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23769
    | (have j0 := eq23769 X0 X1 X2
       grind)
    | exact resolve eq23769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23769
  have eq36451 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq327 X0 X1
       have i₂ := eq6332 X0 X2
       grind)
    | exact superpose eq6332 eq327
    | (have j0 := eq327 X0 X1
       have j1 := eq6332 X0 X2
       grind)
    | exact resolve eq327 eq6332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6332
  have eq36593 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq36451 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36451
  have eq191388 : ∀ X0 X1 X2 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ (M.op X1 (M.op (M.op X1 X1) X1))))) ∨ (M.op (τ (σ X0)) X2) = (k (τ (σ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (σ (M.op X1 (M.op (M.op X1 X1) X1)))
       have i₂ := eq11897 (σ X0) X1 X2
       grind)
    | exact superpose eq11897 eq34
    | (have j1 := eq11897 (σ X0) X1 X2
       grind)
    | exact resolve eq34 eq11897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11897
  have eq191396 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X1) X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op (τ (σ X0)) X2) = (k (τ (σ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq191388 X0 X1 X2
       have i₂ := eq10 (M.op X1 (M.op (M.op X1 X1) X1))
       grind)
    | exact superpose eq10 eq191388
    | (have j0 := eq191388 X0 X1 X2
       grind)
    | exact resolve eq191388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191388
  have eq191405 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X1) X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op (τ (σ X0)) X2) = (k (τ (σ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq191396 X0 X1 X2
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq191396
    | (have j0 := eq191396 X0 X1 X2
       grind)
    | exact resolve eq191396 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191396
  have eq191413 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op X1 (M.op (M.op X1 X1) X1))) ∨ (M.op (τ (σ X0)) X2) = (k (τ (σ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq191405 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq191405
    | (have j0 := eq191405 X0 X1 X2
       grind)
    | exact resolve eq191405 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191405
  have eq191414 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq191413 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq191413
    | (have j0 := eq191413 X0 X1 X2
       grind)
    | exact resolve eq191413 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191413
  have eq191476 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq191414 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191414
  have eq191478 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq191476 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq191476
    | (have j0 := eq191476 X0 X1
       grind)
    | exact resolve eq191476 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191476
  have eq191487 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X1 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq191478 X0 X1
       have j1 := eq48 X1 X0
       grind)
    | (have r₁ := eq191478 X1 X1
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq191478 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq191478
  have eq191844 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (M.op (M.op X1 X1) X1)))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op X1 (M.op (M.op X1 X1) X1))
       have i₂ := eq191487 (σ X0) X1
       grind)
    | exact superpose eq191487 eq34
    | exact resolve eq34 eq191487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191487
  have eq191878 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (M.op (M.op X1 X1) X1)))) = (τ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq191844 X0 X1
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq191844
    | exact resolve eq191844 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191844
  have eq191958 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (M.op X1 (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq191878 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq191878
    | exact resolve eq191878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191878
  have eq192828 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (τ (M.op X1 (M.op (M.op X1 X1) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (τ (M.op X1 (M.op (M.op X1 X1) X1)))
       have i₂ := eq191958 (σ X0) X1
       grind)
    | exact superpose eq191958 eq34
    | exact resolve eq34 eq191958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq191958
  have eq192870 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k X0 (τ (τ (M.op X1 (M.op (M.op X1 X1) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq192828 X0 X1
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq192828
    | exact resolve eq192828 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192828
  have eq192950 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (τ (M.op X1 (M.op (M.op X1 X1) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq192870 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq192870
    | exact resolve eq192870 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192870
  have eq194444 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ (τ (M.op X1 (M.op (M.op X1 X1) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq233 X0
       have i₂ := eq192950 (τ X0) X1
       grind)
    | exact superpose eq192950 eq233
    | exact resolve eq233 eq192950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq192950
  have eq194490 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X0 (τ (M.op X1 (M.op (M.op X1 X1) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq194444 X0 X1
       have i₂ := eq39 (τ (M.op X1 (M.op (M.op X1 X1) X1))) X0
       grind)
    | exact superpose eq39 eq194444
    | exact resolve eq194444 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq194444
  have eq196644 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq24092 x y X0
       grind)
    | exact superpose eq24092 eq16
    | (have j1 := eq24092 x y X0
       grind)
    | exact resolve eq16 eq24092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24092
  have eq196650 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq196644 X0
       have j1 := eq36593 y X0 x
       grind)
    | (have r₁ := eq196644 X0
       have r₂ := eq36593 y x x
       grind)
    | exact resolve eq196644 eq36593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36593 eq196644
  have eq196720 : ∀ X0 : G, (τ (M.op (σ y) (σ y))) = (τ (M.op (σ y) (τ (M.op X0 (M.op (M.op X0 X0) X0))))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq194490 (σ y) X0
       have i₂ := eq196650 (τ (M.op X0 (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq196650 eq194490
    | exact resolve eq194490 eq196650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194490 eq196650
  have eq196737 : (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq196720 x
       have i₂ := eq1389 x (σ y)
       grind)
    | exact superpose eq1389 eq196720
    | exact resolve eq196720 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389 eq196720
  have eq196777 : (τ (σ y)) = (τ (σ (M.op y y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq196737
       have i₂ := eq235 y
       grind)
    | exact superpose eq235 eq196737
    | exact resolve eq196737 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq196737
  have eq196800 : (M.op y y) = (τ (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq196777
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq196777
    | exact resolve eq196777 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196777
  have eq196804 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq196800
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq196800
    | exact resolve eq196800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196800
  have eq196844 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq196804
       grind)
    | exact superpose eq196804 eq9
    | exact resolve eq9 eq196804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196868 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq597 y X0
       have i₂ := eq196804
       grind)
    | exact superpose eq196804 eq597
    | exact resolve eq597 eq196804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq197703 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq196844 X0
       have i₂ := eq196804
       grind)
    | exact superpose eq196804 eq196844
    | exact resolve eq196844 eq196804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196804
  have eq197712 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq197703 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197703
  have eq197859 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq196844 X0
       have i₂ := eq197712 y
       grind)
    | exact superpose eq197712 eq196844
    | exact resolve eq196844 eq197712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196844
  have eq197860 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq197859 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197859
  have eq201660 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq196868 X0
       have i₂ := eq197712 y
       grind)
    | exact superpose eq197712 eq196868
    | exact resolve eq196868 eq197712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196868 eq197712
  have eq201673 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq201660 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201660
  have eq201924 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq201673 (σ x)
       grind)
    | exact superpose eq201673 eq16
    | exact resolve eq16 eq201673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201673
  have eq202251 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq201924
       have i₂ := eq197860 x
       grind)
    | exact superpose eq197860 eq201924
    | exact resolve eq201924 eq197860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197860 eq201924
  have eq202252 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by grind
  clear eq202251
  have eq202253 : x = (M.op x x) := by grind
  clear eq202252
  have eq202260 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq202253
       grind)
    | exact superpose eq202253 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq202253
       grind)
    | exact resolve eq12 eq202253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202284 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq327 x X0
       have i₂ := eq202253
       grind)
    | exact superpose eq202253 eq327
    | (have j0 := eq327 x X0
       grind)
    | exact resolve eq327 eq202253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq202253
  have eq202470 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq202284 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202284
  have eq202472 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq202260 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202260
  have eq220556 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq202470 (σ X0)
       grind)
    | exact superpose eq202470 eq15
    | exact resolve eq15 eq202470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202470
  have eq220699 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq220556 X0
       have i₂ := eq202472 X0
       grind)
    | exact superpose eq202472 eq220556
    | exact resolve eq220556 eq202472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202472 eq220556
  have eq238052 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq220699 y
       grind)
    | exact superpose eq220699 eq16
    | (have r₁ := eq16
       have r₂ := eq220699 y
       grind)
    | exact resolve eq16 eq220699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220699
  have eq238263 : False := by grind
  exact eq238263

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pyx_Equation643 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law643 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) ≠ (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (M.op X0 (M.op (M.op X0 X0) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 (M.op (M.op X0 X0) X0))
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X1 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op (M.op X1 X1) X1))
       have r₂ := eq9 (M.op X1 (M.op (M.op X1 X1) X1)) X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X1 (M.op X0 (M.op (M.op X0 X0) X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) (τ X1)
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq74 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq96 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 (M.op X2 (M.op (M.op X2 X2) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq48 X2 X0
       grind)
    | exact superpose eq48 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq48 X2 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq12 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq103 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 (M.op X2 (M.op (M.op X2 X2) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq96 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq206 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq73 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq207 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq206 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq213 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq207 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq207 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq207 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq223 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq213 (σ X0)
       grind)
    | exact superpose eq213 eq15
    | exact resolve eq15 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq223 X0
       have i₂ := eq213 X0
       grind)
    | exact superpose eq213 eq223
    | exact resolve eq223 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq322 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq232 X0
       grind)
    | exact superpose eq232 eq9
    | exact resolve eq9 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq232 X0
       grind)
    | exact superpose eq232 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq232 X0
       grind)
    | exact superpose eq232 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq322 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq322
    | exact resolve eq322 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq570 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq520 X0 X1
       have i₂ := eq232 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq232 eq520
    | exact resolve eq520 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq580 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq570 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq570
    | exact resolve eq570 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq582 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 X1
       have i₂ := eq232 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq232 eq580
    | exact resolve eq580 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq584 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq582 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq582
    | exact resolve eq582 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq659 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X0)) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq74 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq74 eq15
    | (have j1 := eq74 (σ X0) X2 X2
       grind)
    | exact resolve eq15 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq691 : ∀ X0 X1 X2 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq659 X0 X1 X2
       have i₂ := eq232 X1
       grind)
    | exact superpose eq232 eq659
    | (have j0 := eq659 X0 X1 X2
       grind)
    | exact resolve eq659 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq2485 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) ≠ X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq2487 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2485 X0 X1
       grind)
    | (have r₁ := eq2485 X0 X1
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq2485 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485
  have eq5542 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq5744 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5542 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5542
    | (have j0 := eq5542 X0 X0
       grind)
    | exact resolve eq5542 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5542
  have eq59982 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq691 X1 X0 X2
       grind)
    | exact superpose eq691 eq10
    | (have j1 := eq691 X1 X0 X2
       grind)
    | exact resolve eq10 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq60726 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59982 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59982
    | (have j0 := eq59982 X0 X1 X2
       grind)
    | exact resolve eq59982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59982
  have eq123110 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324 X0 X1
       have i₂ := eq5744 X2 X0
       grind)
    | exact superpose eq5744 eq324
    | (have j0 := eq324 X0 X1
       have j1 := eq5744 X2 X0
       grind)
    | exact resolve eq324 eq5744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq5744
  have eq123258 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq123110 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123110
  have eq196202 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq60726 y x X0
       grind)
    | exact superpose eq60726 eq16
    | (have j1 := eq60726 y x X0
       grind)
    | exact resolve eq16 eq60726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60726
  have eq196208 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op X0 X0) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq196202 X0
       have j1 := eq123258 x X0 X0
       grind)
    | (have r₁ := eq196202 X0
       have r₂ := eq123258 x x y
       grind)
    | exact resolve eq196202 eq123258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123258 eq196202
  have eq196236 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq213 (σ x)
       have i₂ := eq196208 (σ x)
       grind)
    | exact superpose eq196208 eq213
    | (have j1 := eq196208 (σ x)
       grind)
    | exact resolve eq213 eq196208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq196208
  have eq196407 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq196236
  have eq196498 : (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq196407
       have i₂ := eq232 x
       grind)
    | exact superpose eq232 eq196407
    | exact resolve eq196407 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq196407
  have eq196575 : (M.op x x) = (τ (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq196498
       grind)
    | exact superpose eq196498 eq10
    | exact resolve eq10 eq196498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196498
  have eq196654 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq196575
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq196575
    | exact resolve eq196575 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196575
  have eq196726 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq196654
       grind)
    | exact superpose eq196654 eq9
    | exact resolve eq9 eq196654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196727 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq196654
       grind)
    | exact superpose eq196654 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq196654
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq196654
       grind)
    | exact resolve eq12 eq196654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196756 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq584 y X0
       have i₂ := eq196654
       grind)
    | exact superpose eq196654 eq584
    | exact resolve eq584 eq196654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq196793 : ∀ X0 : G, (k X0 (M.op y (M.op y y))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2487 X0 y
       have i₂ := eq196654
       grind)
    | exact superpose eq196654 eq2487
    | exact resolve eq2487 eq196654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2487
  have eq196936 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq196727 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196727
  have eq197677 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq196726 X0
       have i₂ := eq196654
       grind)
    | exact superpose eq196654 eq196726
    | exact resolve eq196726 eq196654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196654
  have eq197704 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq197677 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197677
  have eq197884 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq196726 X0
       have i₂ := eq197704 y
       grind)
    | exact superpose eq197704 eq196726
    | exact resolve eq196726 eq197704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196726 eq197704
  have eq197889 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq197884 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197884
  have eq199679 : ∀ X0 : G, (k X0 (M.op y y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq196793 X0
       have i₂ := eq197889 y
       grind)
    | exact superpose eq197889 eq196793
    | exact resolve eq196793 eq197889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196793
  have eq199762 : ∀ X0 : G, (k X0 (M.op y y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq199679 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199679
  have eq200648 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op y y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op y y)
       have i₂ := eq199762 (τ X0)
       grind)
    | exact superpose eq199762 eq17
    | exact resolve eq17 eq199762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq199762
  have eq200716 : ∀ X0 : G, (k X0 (σ (M.op y y))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq200648 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq200648
    | exact resolve eq200648 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200648
  have eq202205 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op y y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (M.op y y)
       have i₂ := eq200716 (σ X0)
       grind)
    | exact superpose eq200716 eq15
    | exact resolve eq15 eq200716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200716
  have eq205073 : (σ y) = (σ (M.op y (M.op y y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq202205 y
       have i₂ := eq196936 (M.op y y)
       grind)
    | exact superpose eq196936 eq202205
    | exact resolve eq202205 eq196936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196936 eq202205
  have eq205122 : (σ y) = (σ (M.op y (M.op y y))) ∨ x = (M.op x x) := by grind
  clear eq205073
  have eq206572 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq196756 X0
       have i₂ := eq205122
       grind)
    | exact superpose eq205122 eq196756
    | exact resolve eq196756 eq205122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196756 eq205122
  have eq206585 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq206572 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206572
  have eq206841 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq206585 (σ x)
       grind)
    | exact superpose eq206585 eq16
    | exact resolve eq16 eq206585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206585
  have eq207201 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq206841
       have i₂ := eq197889 x
       grind)
    | exact superpose eq197889 eq206841
    | exact resolve eq206841 eq197889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197889 eq206841
  have eq207202 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by grind
  clear eq207201
  have eq207203 : x = (M.op x x) := by grind
  clear eq207202
  have eq207208 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq207203
       grind)
    | exact superpose eq207203 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq207203
       grind)
    | exact resolve eq12 eq207203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207239 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq323 x X0
       have i₂ := eq207203
       grind)
    | exact superpose eq207203 eq323
    | (have j0 := eq323 x X0
       grind)
    | exact resolve eq323 eq207203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq207203
  have eq207470 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq207239 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207239
  have eq207472 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq207208 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207208
  have eq219530 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq207470 (σ X0)
       grind)
    | exact superpose eq207470 eq15
    | exact resolve eq15 eq207470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207470
  have eq219776 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq219530 X0
       have i₂ := eq207472 X0
       grind)
    | exact superpose eq207472 eq219530
    | exact resolve eq219530 eq207472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207472 eq219530
  have eq226555 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq219776 y
       grind)
    | exact superpose eq219776 eq16
    | (have r₁ := eq16
       have r₂ := eq219776 y
       grind)
    | exact resolve eq16 eq219776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219776
  have eq226799 : False := by grind
  exact eq226799

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation643 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law643 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq41 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq111 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41 x y
       grind)
    | exact superpose eq41 eq16
    | (have j1 := eq41 x y
       grind)
    | exact resolve eq16 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq496 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq117 (τ X1) (τ X0)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq117
    | (have j0 := eq117 (τ X1) (τ X0)
       grind)
    | exact resolve eq117 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq496 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq496
    | (have j0 := eq496 X0 X1
       grind)
    | exact resolve eq496 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq508 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq505 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq505
    | (have j0 := eq505 X0 X1
       grind)
    | exact resolve eq505 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq510 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq508 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq508
    | (have j0 := eq508 X0 X1
       grind)
    | exact resolve eq508 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq511 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq510 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq510
    | (have j0 := eq510 X0 X1
       grind)
    | exact resolve eq510 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq512 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq511 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq511
    | (have j0 := eq511 X0 X1
       grind)
    | exact resolve eq511 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq513 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq512
    | (have j0 := eq512 X0 X1
       grind)
    | exact resolve eq512 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq532 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq118 (τ X1) (τ X0)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq118
    | (have j0 := eq118 (τ X1) (τ X0)
       grind)
    | exact resolve eq118 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq542 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq532
    | (have j0 := eq532 X0 X1
       grind)
    | exact resolve eq532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq545 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq542 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq542
    | (have j0 := eq542 X0 X1
       grind)
    | exact resolve eq542 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq547 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq545 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq545
    | (have j0 := eq545 X0 X1
       grind)
    | exact resolve eq545 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq548 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq547 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq547
    | (have j0 := eq547 X0 X1
       grind)
    | exact resolve eq547 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq549 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq548
    | (have j0 := eq548 X0 X1
       grind)
    | exact resolve eq548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq550 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq549 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq549
    | (have j0 := eq549 X0 X1
       grind)
    | exact resolve eq549 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq564 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq111
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq111 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq564
  have eq3722 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq565
       grind)
    | exact superpose eq565 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq565
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq565
       grind)
    | exact resolve eq12 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq3724 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3722
  have eq3725 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3724
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3724
    | exact resolve eq3724 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3724
  have eq32262 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3725
       grind)
    | exact superpose eq3725 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3725
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3725
       grind)
    | exact resolve eq13 eq3725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32263 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3725
       grind)
    | exact superpose eq3725 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3725
       grind)
    | exact resolve eq12 eq3725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3725
  have eq32264 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq32262
  have eq32267 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32263
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq32263
    | exact resolve eq32263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32263
  have eq32268 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq32267
  have eq32269 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32264
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq32264
    | exact resolve eq32264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32264
  have eq32271 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq32269
       have r₂ := eq32268
       grind)
    | exact resolve eq32269 eq32268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32268 eq32269
  have eq33169 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq32271
       grind)
    | exact superpose eq32271 eq10
    | exact resolve eq10 eq32271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32271
  have eq33332 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33169
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq33169
    | exact resolve eq33169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33169
  have eq33335 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq550 y x
       grind)
    | (have r₁ := eq33332
       have r₂ := eq550 y x
       grind)
    | exact resolve eq33332 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq33332
  have eq33691 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq33335
       grind)
    | exact superpose eq33335 eq10
    | exact resolve eq10 eq33335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33335
  have eq33856 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33691
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq33691
    | exact resolve eq33691 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33691
  have eq33857 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq513 y x
       grind)
    | (have r₁ := eq33856
       have r₂ := eq513 y x
       grind)
    | exact resolve eq33856 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq33856
  have eq34199 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq33857
       grind)
    | exact superpose eq33857 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq33857
       grind)
    | exact resolve eq12 eq33857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34200 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq34201 : x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq34199
  have eq34865 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117 x y
       have i₂ := eq34201
       grind)
    | exact superpose eq34201 eq117
    | (have j0 := eq117 x y
       grind)
    | exact resolve eq117 eq34201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq34910 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq34865
  have eq41498 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34910
       grind)
    | exact superpose eq34910 eq16
    | exact resolve eq16 eq34910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34910
  have eq42976 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41498
       have i₂ := eq33857
       grind)
    | exact superpose eq33857 eq41498
    | exact resolve eq41498 eq33857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41498
  have eq42979 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq42976
  have eq42980 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq42979
       have r₂ := eq34200
       grind)
    | exact resolve eq42979 eq34200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42979
  have eq43463 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42980
       grind)
    | exact superpose eq42980 eq16
    | exact resolve eq16 eq42980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43464 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq42980
       grind)
    | exact superpose eq42980 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq42980
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq42980
       grind)
    | exact resolve eq13 eq42980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42980
  have eq43466 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq43464
  have eq43470 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43466
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq43466
    | exact resolve eq43466 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43466
  have eq43978 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43463
       have i₂ := eq33857
       grind)
    | exact superpose eq33857 eq43463
    | exact resolve eq43463 eq33857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33857 eq43463
  have eq43982 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq43978
       have r₂ := eq34200
       grind)
    | exact resolve eq43978 eq34200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34200 eq43978
  have eq45220 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43470
       have i₂ := eq34201
       grind)
    | exact superpose eq34201 eq43470
    | exact resolve eq43470 eq34201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34201 eq43470
  have eq45393 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq45220
  have eq45545 : x = (M.op x y) := by
    first
    | (have r₁ := eq45393
       have r₂ := eq43982
       grind)
    | exact resolve eq45393 eq43982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43982 eq45393
  have eq45986 : x ≠ x ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq45545
       grind)
    | exact superpose eq45545 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq45545
       grind)
    | exact resolve eq13 eq45545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45987 : x ≠ y ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq45545
       grind)
    | exact superpose eq45545 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq45545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45988 : y = (k y x) ∨ x = y := by grind
  clear eq45986
  have eq46800 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq118 x y
       have i₂ := eq45988
       grind)
    | exact superpose eq45988 eq118
    | (have j0 := eq118 x y
       grind)
    | exact resolve eq118 eq45988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq46826 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq46800
  have eq49727 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq46826
       grind)
    | exact superpose eq46826 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq46826
       grind)
    | exact resolve eq12 eq46826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46826
  have eq49729 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq49727
  have eq49730 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq49729
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq49729
    | exact resolve eq49729 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49729
  have eq50591 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq49730
       grind)
    | exact superpose eq49730 eq16
    | exact resolve eq16 eq49730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49730
  have eq50600 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq50591
       have i₂ := eq45545
       grind)
    | exact superpose eq45545 eq50591
    | exact resolve eq50591 eq45545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50591
  have eq50601 : (σ x) = (σ (k y x)) ∨ x = y := by grind
  clear eq50600
  have eq51017 : (k y x) = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq50601
       grind)
    | exact superpose eq50601 eq10
    | exact resolve eq10 eq50601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50601
  have eq51262 : x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq51017
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq51017
    | exact resolve eq51017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51017
  have eq51263 : x = (k y x) := by
    first
    | (have r₁ := eq51262
       have r₂ := eq45987
       grind)
    | exact resolve eq51262 eq45987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45987 eq51262
  have eq51725 : x = y ∨ x = y := by
    first
    | (have i₁ := eq45988
       have i₂ := eq51263
       grind)
    | exact superpose eq51263 eq45988
    | exact resolve eq45988 eq51263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45988
  have eq51756 : x = y := by grind
  clear eq51725
  have eq52164 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51756
       grind)
    | exact superpose eq51756 eq16
    | exact resolve eq16 eq51756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52165 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq51756
       grind)
    | exact superpose eq51756 eq111
    | exact resolve eq111 eq51756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq52197 : x = (M.op x x) := by
    first
    | (have i₁ := eq45545
       have i₂ := eq51756
       grind)
    | exact superpose eq51756 eq45545
    | exact resolve eq45545 eq51756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45545
  have eq52199 : x = (k x x) := by
    first
    | (have i₁ := eq51263
       have i₂ := eq51756
       grind)
    | exact superpose eq51756 eq51263
    | exact resolve eq51263 eq51756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51263 eq51756
  have eq52228 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq52165
  have eq52229 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq52228
       have i₂ := eq52199
       grind)
    | exact superpose eq52199 eq52228
    | exact resolve eq52228 eq52199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52199 eq52228
  have eq52230 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq52164
       have i₂ := eq52197
       grind)
    | exact superpose eq52197 eq52164
    | exact resolve eq52164 eq52197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52164
  have eq52231 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq52229
       have i₂ := eq52197
       grind)
    | exact superpose eq52197 eq52229
    | exact resolve eq52229 eq52197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52197 eq52229
  have eq52232 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq52231
  have eq52233 : False := by grind
  exact eq52233

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_pxy_pyx_Equation643 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law643 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) ≠ (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X1) = (k X1 (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 (M.op (M.op X0 X0) X0))
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op (M.op X1 X1) X1))
       have r₂ := eq9 (M.op X1 (M.op (M.op X1 X1) X1)) X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) ≠ (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X1) = X1 ∨ (k (M.op X0 (M.op (M.op X0 X0) X0)) X1) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       grind)
    | (have r₁ := eq13 (M.op X1 (M.op (M.op X1 X1) X1)) X1
       have r₂ := eq9 (M.op X1 (M.op (M.op X1 X1) X1)) X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k (M.op X0 (M.op (M.op X0 X0) X0)) X1) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq70 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq73 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq178 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq73 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq179 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq178 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq183 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq179 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq179 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq179 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq187 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq183 (σ X0)
       grind)
    | exact superpose eq183 eq15
    | exact resolve eq15 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0 X0
       have i₂ := eq183 (τ X0)
       grind)
    | exact superpose eq183 eq39
    | exact resolve eq39 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq189 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq189
    | exact resolve eq189 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq200 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq187 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq187
    | exact resolve eq187 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq187
  have eq305 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq200 X0
       grind)
    | exact superpose eq200 eq9
    | exact resolve eq9 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq198 X0
       grind)
    | exact superpose eq198 eq9
    | exact resolve eq9 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 (M.op (M.op X1 X1) X1))) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X1 (τ X0)
       have i₂ := eq198 X0
       grind)
    | exact superpose eq198 eq38
    | exact resolve eq38 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq305 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq305
    | exact resolve eq305 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq558 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq505 X0 X1
       have i₂ := eq200 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq200 eq505
    | exact resolve eq505 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq566 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq558
    | exact resolve eq558 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq568 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq566 X0 X1
       have i₂ := eq200 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq200 eq566
    | exact resolve eq566 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq570 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq568
    | exact resolve eq568 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq626 : ∀ X0 X1 : G, (k (σ (M.op X0 (M.op (M.op X0 X0) X0))) X1) = (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op X0 (M.op (M.op X0 X0) X0))
       have i₂ := eq48 X0 (τ X1)
       grind)
    | exact superpose eq48 eq18
    | (have j1 := eq48 X0 (τ X1)
       grind)
    | exact resolve eq18 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq48
  have eq635 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X1 X1)) ∨ (k (σ (M.op X0 (M.op (M.op X0 X0) X0))) X1) = (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq626 X0 X1
       have i₂ := eq198 X1
       grind)
    | exact superpose eq198 eq626
    | (have j0 := eq626 X0 X1
       grind)
    | exact resolve eq626 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq1081 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (τ (M.op X0 (M.op (M.op X0 X0) X0))) (τ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq408 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq408
    | exact resolve eq408 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq1164 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op X0 (M.op (M.op X0 X0) X0))) (τ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1081 X0 X1
       have i₂ := eq198 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq198 eq1081
    | exact resolve eq1081 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1182 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op X0 (M.op (M.op X0 X0) X0))) (τ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1164 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq1164
    | exact resolve eq1164 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq1187 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1182 X0 X1
       have i₂ := eq198 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq198 eq1182
    | exact resolve eq1182 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1192 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1187 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq1187
    | exact resolve eq1187 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1270 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) (M.op X1 (M.op (M.op X1 X1) X1))) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X1 (σ X0)
       have i₂ := eq68 X2 X0
       grind)
    | exact superpose eq68 eq38
    | (have j1 := eq68 X2 X0
       grind)
    | exact resolve eq38 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq68
  have eq1333 : ∀ X0 X1 X2 : G, (σ X2) = (σ (M.op X2 X2)) ∨ (σ X0) = (k (σ X0) (M.op X1 (M.op (M.op X1 X1) X1))) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1270 X0 X1 X2
       have i₂ := eq200 X2
       grind)
    | exact superpose eq200 eq1270
    | (have j0 := eq1270 X0 X1 X2
       grind)
    | exact resolve eq1270 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270
  have eq1457 : ∀ X0 X1 : G, (τ (M.op X0 (M.op (M.op X0 X0) X0))) ≠ (τ (M.op X0 (M.op (M.op X0 X0) X0))) ∨ (M.op X1 X1) = (k X1 (τ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ (M.op X0 (M.op (M.op X0 X0) X0)))
       have i₂ := eq1192 X0 (τ (M.op X0 (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq1192 eq12
    | (have j0 := eq12 X1 (τ (M.op X0 (M.op (M.op X0 X0) X0)))
       grind)
    | (have r₁ := eq12 X0 (τ (M.op X0 (M.op (M.op X0 X0) X0)))
       have r₂ := eq1192 X0 (τ (M.op X0 (M.op (M.op X0 X0) X0)))
       grind)
    | exact resolve eq12 eq1192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1478 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq1457 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457
  have eq2668 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ (M.op X1 (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0
       have i₂ := eq1478 X1 (τ X0)
       grind)
    | exact superpose eq1478 eq198
    | exact resolve eq198 eq1478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq1478
  have eq2693 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X0 (M.op X1 (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2668 X0 X1
       have i₂ := eq39 (M.op X1 (M.op (M.op X1 X1) X1)) X0
       grind)
    | exact superpose eq39 eq2668
    | exact resolve eq2668 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2668
  have eq8653 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq8945 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8653 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8653
    | (have j0 := eq8653 X0 X0
       grind)
    | exact resolve eq8653 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8653
  have eq133636 : ∀ X0 X1 : G, (k (σ (M.op X1 (M.op (M.op X1 X1) X1))) (σ X0)) = (σ (M.op (M.op X1 (M.op (M.op X1 X1) X1)) X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq635 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq635
    | exact resolve eq635 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq133895 : ∀ X0 X1 : G, (σ (k (M.op X1 (M.op (M.op X1 X1) X1)) X0)) = (σ (M.op (M.op X1 (M.op (M.op X1 X1) X1)) X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq133636 X0 X1
       have i₂ := eq15 (M.op X1 (M.op (M.op X1 X1) X1)) X0
       grind)
    | exact superpose eq15 eq133636
    | (have j0 := eq133636 X0 X1
       grind)
    | exact resolve eq133636 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133636
  have eq134016 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X0 ∨ (σ (k (M.op X1 (M.op (M.op X1 X1) X1)) X0)) = (σ (M.op (M.op X1 (M.op (M.op X1 X1) X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq133895 X0 X1
       have i₂ := eq200 X0
       grind)
    | exact superpose eq200 eq133895
    | (have j0 := eq133895 X0 X1
       grind)
    | exact resolve eq133895 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133895
  have eq134104 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k (M.op X1 (M.op (M.op X1 X1) X1)) X0)) = (σ (M.op (M.op X1 (M.op (M.op X1 X1) X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq134016 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq134016
    | (have j0 := eq134016 X0 X1
       grind)
    | exact resolve eq134016 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134016
  have eq172448 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X1) = (k (σ X1) (M.op X2 (M.op (M.op X2 X2) X2))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq1333 X1 X2 X0
       grind)
    | exact superpose eq1333 eq10
    | (have j1 := eq1333 X1 X2 X0
       grind)
    | exact resolve eq10 eq1333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq172856 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ X1) = (k (σ X1) (M.op X2 (M.op (M.op X2 X2) X2))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq172448 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq172448
    | (have j0 := eq172448 X0 X1 X2
       grind)
    | exact resolve eq172448 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172448
  have eq404030 : ∀ X0 X2 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X2 X2) = X2 ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq2693 (σ X0) x
       have i₂ := eq172856 X2 X0 x
       grind)
    | exact superpose eq172856 eq2693
    | (have j1 := eq172856 X2 X0 X2
       grind)
    | exact resolve eq2693 eq172856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2693 eq172856
  have eq404031 : ∀ X0 X2 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (M.op X2 X2) = X2 ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq404030 X0 X2
       have i₂ := eq200 X0
       grind)
    | exact superpose eq200 eq404030
    | (have j0 := eq404030 X0 X2
       grind)
    | exact resolve eq404030 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq404030
  have eq404035 : ∀ X0 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X2 X2) = X2 ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq404031 X0 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq404031
    | (have j0 := eq404031 X0 X2
       grind)
    | exact resolve eq404031 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404031
  have eq404036 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X2 X2) = X2 ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq404035 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq404035
    | (have j0 := eq404035 X0 X2
       grind)
    | exact resolve eq404035 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404035
  have eq429634 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq404036 y x
       grind)
    | exact superpose eq404036 eq16
    | (have j1 := eq404036 y y
       grind)
    | exact resolve eq16 eq404036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404036
  have eq429644 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq8945 y y
       grind)
    | (have r₁ := eq429634
       have r₂ := eq8945 y x
       grind)
    | exact resolve eq429634 eq8945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8945 eq429634
  have eq429671 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq429644
       grind)
    | exact superpose eq429644 eq9
    | exact resolve eq9 eq429644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429696 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq570 y X0
       have i₂ := eq429644
       grind)
    | exact superpose eq429644 eq570
    | exact resolve eq570 eq429644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432440 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq429671 X0
       have i₂ := eq429644
       grind)
    | exact superpose eq429644 eq429671
    | exact resolve eq429671 eq429644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429644
  have eq432461 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq432440 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432440
  have eq432586 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq429671 X0
       have i₂ := eq432461 y
       grind)
    | exact superpose eq432461 eq429671
    | exact resolve eq429671 eq432461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429671
  have eq432587 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq432586 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432586
  have eq439013 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq429696 X0
       have i₂ := eq432461 y
       grind)
    | exact superpose eq432461 eq429696
    | exact resolve eq429696 eq432461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429696 eq432461
  have eq439016 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq439013 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439013
  have eq439287 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq439016 (σ x)
       grind)
    | exact superpose eq439016 eq16
    | exact resolve eq16 eq439016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439016
  have eq439769 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq439287
       have i₂ := eq432587 x
       grind)
    | exact superpose eq432587 eq439287
    | exact resolve eq439287 eq432587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432587 eq439287
  have eq439770 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by grind
  clear eq439769
  have eq439771 : x = (M.op x x) := by grind
  clear eq439770
  have eq439774 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq439771
       grind)
    | exact superpose eq439771 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq439771
       grind)
    | exact resolve eq12 eq439771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439812 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (M.op x (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq413 X0 x
       have i₂ := eq439771
       grind)
    | exact superpose eq439771 eq413
    | exact resolve eq413 eq439771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq439817 : ∀ X0 : G, (M.op X0 (σ (M.op x (M.op x x)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq570 x X0
       have i₂ := eq439771
       grind)
    | exact superpose eq439771 eq570
    | exact resolve eq570 eq439771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440113 : ∀ X0 : G, (σ (k (M.op x (M.op x x)) X0)) = (σ (M.op (M.op x (M.op x x)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq134104 X0 x
       have i₂ := eq439771
       grind)
    | exact superpose eq439771 eq134104
    | (have j0 := eq134104 X0 x
       grind)
    | exact resolve eq134104 eq439771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134104
  have eq440280 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq439774 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439774
  have eq440389 : ∀ X0 : G, (σ (k (M.op x x) X0)) = (σ (M.op (M.op x x) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq440113 X0
       have i₂ := eq439771
       grind)
    | exact superpose eq439771 eq440113
    | (have j0 := eq440113 X0
       grind)
    | exact resolve eq440113 eq439771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440113
  have eq440677 : ∀ X0 : G, (M.op X0 (σ (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq439817 X0
       have i₂ := eq439771
       grind)
    | exact superpose eq439771 eq439817
    | exact resolve eq439817 eq439771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439817
  have eq440682 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq439812 X0
       have i₂ := eq439771
       grind)
    | exact superpose eq439771 eq439812
    | exact resolve eq439812 eq439771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439812
  have eq440796 : ∀ X0 : G, (σ (M.op x X0)) = (σ (k x X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq440389 X0
       have i₂ := eq439771
       grind)
    | exact superpose eq439771 eq440389
    | (have j0 := eq440389 X0
       grind)
    | exact resolve eq440389 eq439771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440389
  have eq441064 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq440677 X0
       have i₂ := eq439771
       grind)
    | exact superpose eq439771 eq440677
    | exact resolve eq440677 eq439771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440677
  have eq441069 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq440682 X0
       have i₂ := eq439771
       grind)
    | exact superpose eq439771 eq440682
    | exact resolve eq440682 eq439771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439771 eq440682
  have eq448872 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (σ x) X0
       have i₂ := eq441064 (σ x)
       grind)
    | exact superpose eq441064 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq441064 (σ x)
       grind)
    | exact resolve eq13 eq441064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441064
  have eq449796 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq448872 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448872
  have eq595446 : ∀ X0 : G, (σ (M.op x X0)) = (σ (k x X0)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq440280 X0
       have i₂ := eq440796 X0
       grind)
    | exact superpose eq440796 eq440280
    | (have j1 := eq440796 X0
       grind)
    | exact resolve eq440280 eq440796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440796
  have eq629481 : ∀ X0 : G, (τ X0) = (k (τ X0) x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq441069 X0
       have i₂ := eq449796 X0
       grind)
    | exact superpose eq449796 eq441069
    | (have j1 := eq449796 X0
       grind)
    | exact resolve eq441069 eq449796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441069 eq449796
  have eq705562 : ∀ X0 : G, (k X0 x) = X0 ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq629481 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq629481
    | (have j0 := eq629481 (σ X0)
       grind)
    | exact resolve eq629481 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629481
  have eq705580 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq705562 X0
       have i₂ := eq15 x X0
       grind)
    | exact superpose eq15 eq705562
    | (have j0 := eq705562 X0
       grind)
    | exact resolve eq705562 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705562
  have eq705596 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq705580 y
       grind)
    | exact superpose eq705580 eq16
    | (have j1 := eq705580 y
       grind)
    | exact resolve eq16 eq705580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705580
  have eq705681 : y = (k y x) := by
    first
    | (have j1 := eq595446 y
       grind)
    | (have r₁ := eq705596
       have r₂ := eq595446 y
       grind)
    | exact resolve eq705596 eq595446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595446 eq705596
  have eq705711 : y = (M.op y y) := by
    first
    | (have i₁ := eq705681
       have i₂ := eq440280 y
       grind)
    | exact superpose eq440280 eq705681
    | exact resolve eq705681 eq440280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440280 eq705681
  have eq705776 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq705711
       grind)
    | exact superpose eq705711 eq9
    | exact resolve eq9 eq705711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705802 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq570 y X0
       have i₂ := eq705711
       grind)
    | exact superpose eq705711 eq570
    | exact resolve eq570 eq705711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq706456 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq705802 X0
       have i₂ := eq705711
       grind)
    | exact superpose eq705711 eq705802
    | exact resolve eq705802 eq705711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705802
  have eq706476 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq705776 X0
       have i₂ := eq705711
       grind)
    | exact superpose eq705711 eq705776
    | exact resolve eq705776 eq705711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705776
  have eq706769 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq706456 X0
       have i₂ := eq705711
       grind)
    | exact superpose eq705711 eq706456
    | exact resolve eq706456 eq705711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706456
  have eq706789 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq706476 X0
       have i₂ := eq705711
       grind)
    | exact superpose eq705711 eq706476
    | exact resolve eq706476 eq705711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705711 eq706476
  have eq711653 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq706769 (σ x)
       grind)
    | exact superpose eq706769 eq16
    | exact resolve eq16 eq706769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706769
  have eq711969 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq711653
       have i₂ := eq706789 x
       grind)
    | exact superpose eq706789 eq711653
    | exact resolve eq711653 eq706789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706789 eq711653
  have eq711970 : False := by grind
  exact eq711970

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyx_y_pxy_Equation643 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law643 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) ≠ (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X1) = X1 ∨ (k (M.op X0 (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       grind)
    | (have r₁ := eq13 (M.op X1 (M.op (M.op X1 X1) X1)) X1
       have r₂ := eq9 (M.op X1 (M.op (M.op X1 X1) X1)) X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k (M.op X0 (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq73 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq74 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq96 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k (M.op X2 (M.op (M.op X2 X2) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq48 X2 X0
       grind)
    | exact superpose eq48 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq48 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq12 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq103 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (k (M.op X2 (M.op (M.op X2 X2) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq96 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq208 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq73 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq209 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq208 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq215 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq209 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq209 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq209 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq225 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq215 (σ X0)
       grind)
    | exact superpose eq215 eq15
    | exact resolve eq15 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq225 X0
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq225
    | exact resolve eq225 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq322 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq234 X0
       grind)
    | exact superpose eq234 eq9
    | exact resolve eq9 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq234 X0
       grind)
    | exact superpose eq234 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq234 X0
       grind)
    | exact superpose eq234 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq322 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq322
    | exact resolve eq322 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq570 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq520 X0 X1
       have i₂ := eq234 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq234 eq520
    | exact resolve eq520 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq580 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq570 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq570
    | exact resolve eq570 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq582 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 X1
       have i₂ := eq234 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq234 eq580
    | exact resolve eq580 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq584 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq582 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq582
    | exact resolve eq582 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq659 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k (σ X0) X2) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq74 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq74 eq15
    | (have j1 := eq74 (σ X0) X2 X2
       grind)
    | exact resolve eq15 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq689 : ∀ X0 X1 X2 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k (σ X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq659 X0 X1 X2
       have i₂ := eq234 X1
       grind)
    | exact superpose eq234 eq659
    | (have j0 := eq659 X0 X1 X2
       grind)
    | exact resolve eq659 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq2494 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X0) X0))) ≠ X1 ∨ (k (M.op X0 (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq103 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq2496 : ∀ X0 X1 : G, (k (M.op X0 (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2494 X0 X1
       grind)
    | (have r₁ := eq2494 X1 X0
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq2494 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2494
  have eq5609 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70
    | (have j0 := eq70 X0 X0
       grind)
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq5806 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5609 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5609
    | (have j0 := eq5609 X0 X0
       grind)
    | exact resolve eq5609 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5609
  have eq60004 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X2 X2) = X2 ∨ (k (σ X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq689 X1 X0 X2
       grind)
    | exact superpose eq689 eq10
    | (have j1 := eq689 X1 X0 X2
       grind)
    | exact resolve eq10 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq60735 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X2 X2) = X2 ∨ (k (σ X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60004 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60004
    | (have j0 := eq60004 X0 X1 X2
       grind)
    | exact resolve eq60004 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60004
  have eq125573 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = X1 ∨ (σ (k X0 X2)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324 X0 X1
       have i₂ := eq5806 X0 X2
       grind)
    | exact superpose eq5806 eq324
    | (have j0 := eq324 X0 X1
       have j1 := eq5806 X0 X2
       grind)
    | exact resolve eq324 eq5806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq5806
  have eq125906 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = X1 ∨ (σ (k X0 X2)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq125573 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125573
  have eq208767 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq60735 y x X0
       grind)
    | exact superpose eq60735 eq16
    | (have j1 := eq60735 y x X0
       grind)
    | exact resolve eq16 eq60735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60735
  have eq208773 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq208767 X0
       have j1 := eq125906 x X0 X0
       grind)
    | (have r₁ := eq208767 X0
       have r₂ := eq125906 x x y
       grind)
    | exact resolve eq208767 eq125906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125906 eq208767
  have eq208802 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq215 (σ x)
       have i₂ := eq208773 (σ x)
       grind)
    | exact superpose eq208773 eq215
    | (have j1 := eq208773 (σ x)
       grind)
    | exact resolve eq215 eq208773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq208773
  have eq208976 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq208802
  have eq209067 : (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq208976
       have i₂ := eq234 x
       grind)
    | exact superpose eq234 eq208976
    | exact resolve eq208976 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq208976
  have eq209146 : (M.op x x) = (τ (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq209067
       grind)
    | exact superpose eq209067 eq10
    | exact resolve eq10 eq209067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209067
  have eq209225 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq209146
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq209146
    | exact resolve eq209146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209146
  have eq209303 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq209225
       grind)
    | exact superpose eq209225 eq9
    | exact resolve eq9 eq209225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209304 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq209225
       grind)
    | exact superpose eq209225 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq209225
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq209225
       grind)
    | exact resolve eq12 eq209225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209339 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq584 y X0
       have i₂ := eq209225
       grind)
    | exact superpose eq209225 eq584
    | exact resolve eq584 eq209225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq209376 : ∀ X0 : G, (k (M.op y (M.op y y)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2496 y X0
       have i₂ := eq209225
       grind)
    | exact superpose eq209225 eq2496
    | exact resolve eq2496 eq209225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2496
  have eq209521 : ∀ X0 : G, (M.op y X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq209304 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209304
  have eq210318 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq209303 X0
       have i₂ := eq209225
       grind)
    | exact superpose eq209225 eq209303
    | exact resolve eq209303 eq209225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209225
  have eq210354 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq210318 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210318
  have eq210577 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq209303 X0
       have i₂ := eq210354 y
       grind)
    | exact superpose eq210354 eq209303
    | exact resolve eq209303 eq210354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209303 eq210354
  have eq210582 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq210577 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210577
  have eq212428 : ∀ X0 : G, (k (M.op y y) X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq209376 X0
       have i₂ := eq210582 y
       grind)
    | exact superpose eq210582 eq209376
    | exact resolve eq209376 eq210582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209376
  have eq212515 : ∀ X0 : G, (k (M.op y y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq212428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212428
  have eq213415 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op y y)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op y y)
       have i₂ := eq212515 (τ X0)
       grind)
    | exact superpose eq212515 eq18
    | exact resolve eq18 eq212515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq212515
  have eq213483 : ∀ X0 : G, (k (σ (M.op y y)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq213415 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq213415
    | exact resolve eq213415 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213415
  have eq214984 : ∀ X0 : G, (σ X0) = (σ (k (M.op y y) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op y y) X0
       have i₂ := eq213483 (σ X0)
       grind)
    | exact superpose eq213483 eq15
    | exact resolve eq15 eq213483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213483
  have eq218423 : (σ y) = (σ (M.op y (M.op y y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq214984 y
       have i₂ := eq209521 (M.op y y)
       grind)
    | exact superpose eq209521 eq214984
    | exact resolve eq214984 eq209521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209521 eq214984
  have eq218473 : (σ y) = (σ (M.op y (M.op y y))) ∨ x = (M.op x x) := by grind
  clear eq218423
  have eq219956 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq209339 X0
       have i₂ := eq218473
       grind)
    | exact superpose eq218473 eq209339
    | exact resolve eq209339 eq218473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209339 eq218473
  have eq219969 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq219956 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219956
  have eq220228 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq219969 (σ x)
       grind)
    | exact superpose eq219969 eq16
    | exact resolve eq16 eq219969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219969
  have eq220598 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq220228
       have i₂ := eq210582 x
       grind)
    | exact superpose eq210582 eq220228
    | exact resolve eq220228 eq210582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210582 eq220228
  have eq220599 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by grind
  clear eq220598
  have eq220600 : x = (M.op x x) := by grind
  clear eq220599
  have eq220606 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq220600
       grind)
    | exact superpose eq220600 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq220600
       grind)
    | exact resolve eq12 eq220600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220637 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq323 x X0
       have i₂ := eq220600
       grind)
    | exact superpose eq220600 eq323
    | (have j0 := eq323 x X0
       grind)
    | exact resolve eq323 eq220600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq220600
  have eq220870 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq220637 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220637
  have eq220872 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq220606 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220606
  have eq233076 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq220870 (σ X0)
       grind)
    | exact superpose eq220870 eq15
    | exact resolve eq15 eq220870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220870
  have eq233254 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq233076 X0
       have i₂ := eq220872 X0
       grind)
    | exact superpose eq220872 eq233076
    | exact resolve eq233076 eq220872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220872 eq233076
  have eq240109 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq233254 y
       grind)
    | exact superpose eq233254 eq16
    | (have r₁ := eq16
       have r₂ := eq233254 y
       grind)
    | exact resolve eq16 eq233254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233254
  have eq240355 : False := by grind
  exact eq240355

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_pxy_pyx_Equation643 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law643 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
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
  have eq51 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (M.op X1 X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq65 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq10
    | (have j1 := eq57 X1 X0
       grind)
    | exact resolve eq10 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq157 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq148
    | (have j0 := eq148 X0 X1
       grind)
    | exact resolve eq148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq264 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq299 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq264 X0 X1
       have i₂ := eq22 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq22 eq264
    | exact resolve eq264 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq306 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq299 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq299
    | exact resolve eq299 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq310 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq22 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq22 eq306
    | exact resolve eq306 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq314 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq310
    | exact resolve eq310 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq1111 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1169 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1111 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1111
    | (have j0 := eq1111 (M.op X1 X1) X1
       grind)
    | exact resolve eq1111 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1877 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq157 y x
       grind)
    | exact superpose eq157 eq16
    | (have j1 := eq157 y x
       grind)
    | exact resolve eq16 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq20026 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1877
       have i₂ := eq1169 x y
       grind)
    | exact superpose eq1169 eq1877
    | (have j1 := eq1169 (M.op y y) y
       grind)
    | (have r₁ := eq1877
       have r₂ := eq1169 x y
       grind)
    | (have r₁ := eq1877
       have r₂ := eq1169 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1877
       have r₂ := eq1169 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1877 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq1877
  have eq20027 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20026
  have eq20028 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20027
  have eq20032 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq20028
       grind)
    | exact superpose eq20028 eq9
    | exact resolve eq9 eq20028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20055 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq314 y X0
       have i₂ := eq20028
       grind)
    | exact superpose eq20028 eq314
    | exact resolve eq314 eq20028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq20343 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20032 X0
       have i₂ := eq20028
       grind)
    | exact superpose eq20028 eq20032
    | exact resolve eq20032 eq20028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20028
  have eq20428 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq20343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20343
  have eq20758 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20032 X0
       have i₂ := eq20428 y
       grind)
    | exact superpose eq20428 eq20032
    | exact resolve eq20032 eq20428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20032
  have eq20759 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq20758 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20758
  have eq21834 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20055 X0
       have i₂ := eq20428 y
       grind)
    | exact superpose eq20428 eq20055
    | exact resolve eq20055 eq20428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20055 eq20428
  have eq21947 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq21834 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21834
  have eq22445 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq21947 (σ x)
       grind)
    | exact superpose eq21947 eq16
    | exact resolve eq16 eq21947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21947
  have eq23335 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22445
       have i₂ := eq20759 x
       grind)
    | exact superpose eq20759 eq22445
    | exact resolve eq22445 eq20759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20759 eq22445
  have eq23336 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23335
  have eq23337 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq23336
  have eq23602 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23337
       grind)
    | exact superpose eq23337 eq10
    | exact resolve eq10 eq23337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23337
  have eq23675 : x = y ∨ x = y := by
    first
    | (have i₁ := eq23602
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23602
    | exact resolve eq23602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23602
  have eq23676 : x = y := by grind
  clear eq23675
  have eq23934 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23676
       grind)
    | exact superpose eq23676 eq16
    | exact resolve eq16 eq23676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23676
  have eq23935 : False := by grind
  exact eq23935

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_pyy_pyx_Equation643 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law643 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
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
  have eq51 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (M.op X1 X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq65 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq10
    | (have j1 := eq57 X1 X0
       grind)
    | exact resolve eq10 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq261 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq250
    | (have j0 := eq250 X0 X1
       grind)
    | exact resolve eq250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq309 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq350 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq309 X0 X1
       have i₂ := eq22 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq22 eq309
    | exact resolve eq309 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq357 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq350 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq350
    | exact resolve eq350 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq361 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq357 X0 X1
       have i₂ := eq22 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq22 eq357
    | exact resolve eq357 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq365 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq361
    | exact resolve eq361 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq1220 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1284 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1220 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1220
    | (have j0 := eq1220 (M.op X1 X1) X1
       grind)
    | exact resolve eq1220 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq2024 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq261 y x
       grind)
    | exact superpose eq261 eq16
    | (have j1 := eq261 y x
       grind)
    | exact resolve eq16 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq32482 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2024
       have i₂ := eq1284 x y
       grind)
    | exact superpose eq1284 eq2024
    | (have j1 := eq1284 (M.op y y) y
       grind)
    | (have r₁ := eq2024
       have r₂ := eq1284 x y
       grind)
    | (have r₁ := eq2024
       have r₂ := eq1284 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2024
       have r₂ := eq1284 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2024 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284 eq2024
  have eq32483 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq32482
  have eq32484 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq32483
  have eq33277 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq32484
       grind)
    | exact superpose eq32484 eq9
    | exact resolve eq9 eq32484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33304 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq365 y X0
       have i₂ := eq32484
       grind)
    | exact superpose eq32484 eq365
    | exact resolve eq365 eq32484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq33898 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq33277 X0
       have i₂ := eq32484
       grind)
    | exact superpose eq32484 eq33277
    | exact resolve eq33277 eq32484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32484
  have eq34013 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq33898 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33898
  have eq34705 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq33277 X0
       have i₂ := eq34013 y
       grind)
    | exact superpose eq34013 eq33277
    | exact resolve eq33277 eq34013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33277
  have eq34706 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq34705 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34705
  have eq37059 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq33304 X0
       have i₂ := eq34013 y
       grind)
    | exact superpose eq34013 eq33304
    | exact resolve eq33304 eq34013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33304 eq34013
  have eq37211 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq37059 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37059
  have eq38595 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq37211 (σ x)
       grind)
    | exact superpose eq37211 eq16
    | exact resolve eq16 eq37211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37211
  have eq40270 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq38595
       have i₂ := eq34706 x
       grind)
    | exact superpose eq34706 eq38595
    | exact resolve eq38595 eq34706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34706 eq38595
  have eq40271 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq40270
  have eq40272 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq40271
  have eq41268 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq40272
       grind)
    | exact superpose eq40272 eq10
    | exact resolve eq10 eq40272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40272
  have eq41345 : x = y ∨ x = y := by
    first
    | (have i₁ := eq41268
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq41268
    | exact resolve eq41268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41268
  have eq41346 : x = y := by grind
  clear eq41345
  have eq42598 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41346
       grind)
    | exact superpose eq41346 eq16
    | exact resolve eq16 eq41346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41346
  have eq42599 : False := by grind
  exact eq42599

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_y_pyx_Equation643 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law643 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
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
  have eq51 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (M.op X1 X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq65 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq10
    | (have j1 := eq57 X1 X0
       grind)
    | exact resolve eq10 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq214 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq203
    | (have j0 := eq203 X0 X1
       grind)
    | exact resolve eq203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq285 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq324 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq285 X0 X1
       have i₂ := eq22 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq22 eq285
    | exact resolve eq285 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq332 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq324 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq324
    | exact resolve eq324 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq336 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq332 X0 X1
       have i₂ := eq22 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq22 eq332
    | exact resolve eq332 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq340 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq336
    | exact resolve eq336 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq1119 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1179 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1119 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1119
    | (have j0 := eq1119 (M.op X1 X1) X1
       grind)
    | exact resolve eq1119 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1976 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq214 y x
       grind)
    | exact superpose eq214 eq16
    | (have j1 := eq214 y x
       grind)
    | exact resolve eq16 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq18651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1976
       have i₂ := eq1179 x y
       grind)
    | exact superpose eq1179 eq1976
    | (have j1 := eq1179 (M.op y y) y
       grind)
    | (have r₁ := eq1976
       have r₂ := eq1179 x y
       grind)
    | (have r₁ := eq1976
       have r₂ := eq1179 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1976
       have r₂ := eq1179 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1976 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179 eq1976
  have eq18652 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18651
  have eq18653 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18652
  have eq18657 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq18653
       grind)
    | exact superpose eq18653 eq9
    | exact resolve eq9 eq18653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18682 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq340 y X0
       have i₂ := eq18653
       grind)
    | exact superpose eq18653 eq340
    | exact resolve eq340 eq18653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq19277 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18657 X0
       have i₂ := eq18653
       grind)
    | exact superpose eq18653 eq18657
    | exact resolve eq18657 eq18653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18653
  have eq19359 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq19277 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19277
  have eq19683 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18657 X0
       have i₂ := eq19359 y
       grind)
    | exact superpose eq19359 eq18657
    | exact resolve eq18657 eq19359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18657
  have eq19684 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq19683 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19683
  have eq20868 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18682 X0
       have i₂ := eq19359 y
       grind)
    | exact superpose eq19359 eq18682
    | exact resolve eq18682 eq19359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18682 eq19359
  have eq20975 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq20868 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20868
  have eq21535 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq20975 (σ x)
       grind)
    | exact superpose eq20975 eq16
    | exact resolve eq16 eq20975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20975
  have eq22486 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21535
       have i₂ := eq19684 x
       grind)
    | exact superpose eq19684 eq21535
    | exact resolve eq21535 eq19684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19684 eq21535
  have eq22487 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22486
  have eq22488 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq22487
  have eq22799 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22488
       grind)
    | exact superpose eq22488 eq10
    | exact resolve eq10 eq22488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22488
  have eq22870 : x = y ∨ x = y := by
    first
    | (have i₁ := eq22799
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22799
    | exact resolve eq22799 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22799
  have eq22871 : x = y := by grind
  clear eq22870
  have eq23201 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22871
       grind)
    | exact superpose eq22871 eq16
    | exact resolve eq16 eq22871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22871
  have eq23202 : False := by grind
  exact eq23202

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyx_pxy_Equation643 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law643 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X1) (σ X1)) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq65 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq10
    | (have j1 := eq57 X1 X0
       grind)
    | exact resolve eq10 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq159 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq150
    | (have j0 := eq150 X0 X1
       grind)
    | exact resolve eq150 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq264 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq299 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq264 X0 X1
       have i₂ := eq22 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq22 eq264
    | exact resolve eq264 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq306 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq299 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq299
    | exact resolve eq299 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq310 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq22 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq22 eq306
    | exact resolve eq306 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq314 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq310
    | exact resolve eq310 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq1111 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1169 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1111 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1111
    | (have j0 := eq1111 (M.op X1 X1) X1
       grind)
    | exact resolve eq1111 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1877 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq159 y x
       grind)
    | exact superpose eq159 eq16
    | (have j1 := eq159 y x
       grind)
    | exact resolve eq16 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq20026 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1877
       have i₂ := eq1169 x y
       grind)
    | exact superpose eq1169 eq1877
    | (have j1 := eq1169 (M.op y y) y
       grind)
    | (have r₁ := eq1877
       have r₂ := eq1169 x y
       grind)
    | (have r₁ := eq1877
       have r₂ := eq1169 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1877
       have r₂ := eq1169 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1877 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq1877
  have eq20027 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20026
  have eq20028 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20027
  have eq20032 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq20028
       grind)
    | exact superpose eq20028 eq9
    | exact resolve eq9 eq20028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20055 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq314 y X0
       have i₂ := eq20028
       grind)
    | exact superpose eq20028 eq314
    | exact resolve eq314 eq20028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq20343 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20032 X0
       have i₂ := eq20028
       grind)
    | exact superpose eq20028 eq20032
    | exact resolve eq20032 eq20028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20028
  have eq20428 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq20343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20343
  have eq20759 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20032 X0
       have i₂ := eq20428 y
       grind)
    | exact superpose eq20428 eq20032
    | exact resolve eq20032 eq20428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20032
  have eq20760 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq20759 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20759
  have eq21861 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20055 X0
       have i₂ := eq20428 y
       grind)
    | exact superpose eq20428 eq20055
    | exact resolve eq20055 eq20428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20055 eq20428
  have eq21974 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq21861 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21861
  have eq22498 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq21974 (σ x)
       grind)
    | exact superpose eq21974 eq16
    | exact resolve eq16 eq21974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21974
  have eq23289 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22498
       have i₂ := eq20760 x
       grind)
    | exact superpose eq20760 eq22498
    | exact resolve eq22498 eq20760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20760 eq22498
  have eq23290 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23289
  have eq23291 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq23290
  have eq23556 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23291
       grind)
    | exact superpose eq23291 eq10
    | exact resolve eq10 eq23291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23291
  have eq23629 : x = y ∨ x = y := by
    first
    | (have i₁ := eq23556
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23556
    | exact resolve eq23556 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23556
  have eq23630 : x = y := by grind
  clear eq23629
  have eq23888 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23630
       grind)
    | exact superpose eq23630 eq16
    | exact resolve eq16 eq23630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23630
  have eq23889 : False := by grind
  exact eq23889

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyy_pxy_Equation643 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law643 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X1) (σ X1)) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq65 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq10
    | (have j1 := eq57 X1 X0
       grind)
    | exact resolve eq10 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq159 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq150
    | (have j0 := eq150 X0 X1
       grind)
    | exact resolve eq150 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq288 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq326 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 X1
       have i₂ := eq22 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq22 eq288
    | exact resolve eq288 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq334 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq326 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq326
    | exact resolve eq326 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq338 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq334 X0 X1
       have i₂ := eq22 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq22 eq334
    | exact resolve eq334 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq342 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq338 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq338
    | exact resolve eq338 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq951 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1007 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq951 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq951
    | (have j0 := eq951 (M.op X1 X1) X1
       grind)
    | exact resolve eq951 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1771 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq159 y x
       grind)
    | exact superpose eq159 eq16
    | (have j1 := eq159 y x
       grind)
    | exact resolve eq16 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq19285 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1771
       have i₂ := eq1007 x y
       grind)
    | exact superpose eq1007 eq1771
    | (have j1 := eq1007 (M.op y y) y
       grind)
    | (have r₁ := eq1771
       have r₂ := eq1007 x y
       grind)
    | (have r₁ := eq1771
       have r₂ := eq1007 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1771
       have r₂ := eq1007 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1771 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq1771
  have eq19286 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19285
  have eq19287 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19286
  have eq19291 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq19287
       grind)
    | exact superpose eq19287 eq9
    | exact resolve eq9 eq19287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19315 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq342 y X0
       have i₂ := eq19287
       grind)
    | exact superpose eq19287 eq342
    | exact resolve eq342 eq19287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq20295 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19291 X0
       have i₂ := eq19287
       grind)
    | exact superpose eq19287 eq19291
    | exact resolve eq19291 eq19287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19287
  have eq20375 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq20295 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20295
  have eq20759 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19291 X0
       have i₂ := eq20375 y
       grind)
    | exact superpose eq20375 eq19291
    | exact resolve eq19291 eq20375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19291
  have eq20760 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq20759 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20759
  have eq21582 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19315 X0
       have i₂ := eq20375 y
       grind)
    | exact superpose eq20375 eq19315
    | exact resolve eq19315 eq20375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19315 eq20375
  have eq21688 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq21582 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21582
  have eq22186 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq21688 (σ x)
       grind)
    | exact superpose eq21688 eq16
    | exact resolve eq16 eq21688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21688
  have eq22997 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22186
       have i₂ := eq20760 x
       grind)
    | exact superpose eq20760 eq22186
    | exact resolve eq22186 eq20760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20760 eq22186
  have eq22998 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22997
  have eq22999 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq22998
  have eq23289 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22999
       grind)
    | exact superpose eq22999 eq10
    | exact resolve eq10 eq22999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22999
  have eq23362 : x = y ∨ x = y := by
    first
    | (have i₁ := eq23289
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23289
    | exact resolve eq23289 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23289
  have eq23363 : x = y := by grind
  clear eq23362
  have eq23735 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23363
       grind)
    | exact superpose eq23363 eq16
    | exact resolve eq16 eq23363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23363
  have eq23736 : False := by grind
  exact eq23736
