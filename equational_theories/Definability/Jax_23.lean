import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
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
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq124 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq127 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq124 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq124 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq124 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq124 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq257 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq127 (σ X0) (σ X1)
       grind)
    | exact superpose eq127 eq15
    | (have j1 := eq127 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq127 (τ X0) X1
       grind)
    | exact superpose eq127 eq18
    | (have j1 := eq127 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq127
  have eq987 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq259 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq259
    | exact resolve eq259 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq1030 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq987 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq987
    | (have j0 := eq987 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq987 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq2191 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq257 x y
       grind)
    | exact superpose eq257 eq16
    | (have j1 := eq257 x y
       grind)
    | exact resolve eq16 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq2408 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2191
       have i₂ := eq1030 x y
       grind)
    | exact superpose eq1030 eq2191
    | (have j1 := eq1030 (σ x) (σ y)
       grind)
    | (have r₁ := eq2191
       have r₂ := eq1030 x y
       grind)
    | (have r₁ := eq2191
       have r₂ := eq1030 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2191
       have r₂ := eq1030 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2191 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030 eq2191
  have eq2409 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2408
  have eq2512 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2409
       grind)
    | exact superpose eq2409 eq10
    | exact resolve eq10 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409
  have eq2558 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2512
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2512
    | exact resolve eq2512 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512
  have eq2559 : x = y := by grind
  clear eq2558
  have eq2699 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2559
       grind)
    | exact superpose eq2559 eq16
    | exact resolve eq16 eq2559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559
  have eq2700 : False := by grind
  exact eq2700

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
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
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq54 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq54 (σ X0) (σ X1)
       grind)
    | exact superpose eq54 eq15
    | (have j1 := eq54 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq54 (τ X0) X1
       grind)
    | exact superpose eq54 eq18
    | (have j1 := eq54 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq54
  have eq307 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq72
    | exact resolve eq72 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq332 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq307
    | (have j0 := eq307 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq307 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq817 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq71 x y
       grind)
    | exact superpose eq71 eq16
    | (have j1 := eq71 x y
       grind)
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq961 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq817
       have i₂ := eq332 x y
       grind)
    | exact superpose eq332 eq817
    | (have j1 := eq332 (σ x) (σ y)
       grind)
    | (have r₁ := eq817
       have r₂ := eq332 x y
       grind)
    | (have r₁ := eq817
       have r₂ := eq332 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq817
       have r₂ := eq332 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq817 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq817
  have eq962 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq961
  have eq997 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq962
       grind)
    | exact superpose eq962 eq10
    | exact resolve eq10 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq1034 : x = y ∨ x = y := by
    first
    | (have i₁ := eq997
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq997
    | exact resolve eq997 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1035 : x = y := by grind
  clear eq1034
  have eq1158 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1035
       grind)
    | exact superpose eq1035 eq16
    | exact resolve eq16 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1159 : False := by grind
  exact eq1159

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
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
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq31 (σ X0)
       grind)
    | exact superpose eq31 eq15
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq33
    | exact resolve eq33 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33
  have eq42 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X2) = (k X1 X2) ∨ X1 = X2 ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X2) = (k X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
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
  have eq58 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (M.op X1 X2) = (k X1 X2) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X0 X2
       have j1 := eq54 X0 X0 X2
       grind)
    | (have r₁ := eq42 X0 X1 X2
       have r₂ := eq54 X0 X1 X2
       grind)
    | (have r₁ := eq42 X1 X0 X2
       have r₂ := eq54 X0 X1 X2
       grind)
    | (have r₁ := eq42 X0 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq54 X0 X1 X2
       grind)
    | exact resolve eq42 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq54
  have eq147 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq148 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq147 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq149 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq239 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq241 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
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
  have eq775 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq241 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq241
    | exact resolve eq241 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq810 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq775 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq775
    | (have j0 := eq775 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq775 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq2130 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq239 x y
       grind)
    | exact superpose eq239 eq16
    | (have j1 := eq239 x y
       grind)
    | exact resolve eq16 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq2274 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2130
       have i₂ := eq810 x y
       grind)
    | exact superpose eq810 eq2130
    | (have j1 := eq810 (σ x) (σ y)
       grind)
    | (have r₁ := eq2130
       have r₂ := eq810 x y
       grind)
    | (have r₁ := eq2130
       have r₂ := eq810 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2130
       have r₂ := eq810 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2130 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq2130
  have eq2275 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2274
  have eq2400 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2275
       grind)
    | exact superpose eq2275 eq10
    | exact resolve eq10 eq2275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2445 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2400
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2400
    | exact resolve eq2400 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2400
  have eq2446 : x = y := by grind
  clear eq2445
  have eq2579 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2446
       grind)
    | exact superpose eq2446 eq16
    | exact resolve eq16 eq2446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446
  have eq2580 : False := by grind
  exact eq2580

/-- `Equation4428`: `x ◇ (x ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pyx_Equation4428 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4428 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4428.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq9 X3 (M.op X3 X2) X4 X5
       have i₂ := eq9 X3 X2 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq9 x X2 X4 X5
       have i₂ := eq9 x X2 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X3 X3) = X3 ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X0 X0
       have i₂ := eq14 X3 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X3 X3
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 X2) X0) ∨ (M.op X3 X3) = X3 ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X0 X1 X2
       have i₂ := eq14 X3 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X3 X3
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq72 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq79 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq72 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq80 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq71 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq84 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq79 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq79 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq79 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq85 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq80 X0 X1 X1
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq80 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq80 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq80 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq86 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 X2) X0) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq70 X0 X1 X2 X3
       have j1 := eq12 X3 X0
       grind)
    | (have r₁ := eq70 X0 X1 X2 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq70 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq87 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq69 X0 X1 X2 X3
       have j1 := eq12 X3 X0
       grind)
    | (have r₁ := eq69 X0 X1 X2 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq69 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq138 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X5 X6) X4) = (M.op (M.op X0 X1) (M.op (M.op X2 X3) X4)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq9 (M.op X2 X3) X4 X5 X6
       have i₂ := eq25 X2 X3 (M.op (M.op X2 X3) X4) X0 X1
       grind)
    | (have i₁ := eq9 (M.op X2 X3) X4 X5 X6
       have i₂ := eq25 X0 X1 (M.op (M.op X2 X3) X4) X2 X3
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq210 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq84 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq211 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq210 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq215 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq211 (σ X0)
       grind)
    | exact superpose eq211 eq15
    | exact resolve eq15 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq215 X0
       have i₂ := eq211 X0
       grind)
    | exact superpose eq211 eq215
    | exact resolve eq215 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq325 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 X3) X4) ≠ (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X4) X4)) ∨ (k (M.op (M.op X2 X3) X4) X5) = (M.op X5 (M.op (M.op X2 X3) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq12 (M.op (M.op X2 X3) X4) X5
       have i₂ := eq23 X2 X3 X4 (M.op (M.op X2 X3) X4) X0 X1
       grind)
    | (have i₁ := eq12 (M.op X3 X2) X1
       have i₂ := eq23 X0 X1 X2 X3 X3 X2
       grind)
    | exact superpose eq23 eq12
    | (have j0 := eq12 (M.op (M.op X2 X3) X4) X5
       grind)
    | exact resolve eq12 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq329 : ∀ X2 X3 X4 X5 : G, (k (M.op (M.op X2 X3) X4) X5) = (M.op X5 (M.op (M.op X2 X3) X4)) := by
    intro X2 X3 X4 X5
    first
    | (have j0 := eq325 x x X2 X3 X4 X5
       grind)
    | (have r₁ := eq325 x x X5 x X3 X5
       have r₂ := eq138 x x (M.op X5 x) X3 X3 X5 x
       grind)
    | exact resolve eq325 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq344 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (σ X0) (σ X0)
       have i₂ := eq226 X0
       grind)
    | exact superpose eq226 eq9
    | exact resolve eq9 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = X2 ∨ (M.op X3 X3) = X3 ∨ (M.op X2 X3) = (k X3 X2) ∨ (k X4 X2) = (M.op X2 X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X3 X2
       have i₂ := eq86 X2 X0 X1 X4
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X2)
       have i₂ := eq86 (M.op X1 X2) X1 X2 X3
       grind)
    | exact superpose eq86 eq14
    | (have j0 := eq14 X3 X3
       have j1 := eq86 X2 X1 X2 X3
       grind)
    | exact resolve eq14 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq883 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = X2 ∨ (M.op X2 X3) = (k X3 X2) ∨ (k X4 X2) = (M.op X2 X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq831 X0 X1 X2 X3 X3
       have j1 := eq12 X3 X2
       grind)
    | (have r₁ := eq831 X0 X1 (M.op X0 X1) X3 X4
       have r₂ := eq12 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq831 X0 X1 X2 X0 X4
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq831 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq1187 : ∀ X0 X1 X2 X3 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (M.op X2 X3)) = (M.op (σ X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq87 (σ X0) X2 X3 (σ X1)
       grind)
    | exact superpose eq87 eq15
    | (have j1 := eq87 (σ X0) X2 X3 X3
       grind)
    | exact resolve eq15 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1689 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = X0 ∨ (M.op X2 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq85 X2 X0 X3
       grind)
    | exact superpose eq85 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq85 X2 X0 X3
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq85 X0 X1 X2
       grind)
    | exact resolve eq12 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1713 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq211 X0
       have i₂ := eq85 X0 X0 X1
       grind)
    | exact superpose eq85 eq211
    | (have j1 := eq85 X0 X0 X1
       grind)
    | exact resolve eq211 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1734 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1713 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq1736 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = X0 ∨ (M.op X2 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1689 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq1821 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1734 X0 (τ X1)
       grind)
    | exact superpose eq1734 eq17
    | (have j1 := eq1734 X0 X1
       grind)
    | exact resolve eq17 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1734
  have eq18054 : ∀ X0 X1 X4 X5 : G, (k (M.op X0 X1) X4) = (M.op X4 (M.op X0 X1)) ∨ (k X5 X0) = (M.op X0 X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq329 x x (M.op (M.op x x) x) X5
       have i₂ := eq87 X0 (M.op x x) x x
       grind)
    | exact superpose eq87 eq329
    | (have j1 := eq87 X4 X1 x (M.op X0 X1)
       grind)
    | exact resolve eq329 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq329
  have eq54115 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1821 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1821
    | (have j0 := eq1821 X1 X1
       grind)
    | exact resolve eq1821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821
  have eq54758 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54115 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq54115
    | (have j0 := eq54115 X0 X1
       grind)
    | exact resolve eq54115 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54115
  have eq56787 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op (σ X0) X2) ∨ (σ (k X3 X0)) = (σ (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq344 X0 X1 X2
       have i₂ := eq54758 X3 X0
       grind)
    | exact superpose eq54758 eq344
    | (have j1 := eq54758 X3 X0
       grind)
    | exact resolve eq344 eq54758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq154145 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1736 X0 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq154147 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq154145 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154145
  have eq154196 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq154147 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154147
  have eq222886 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (M.op X0 X1)) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq1187 x y X0 X1
       grind)
    | exact superpose eq1187 eq16
    | (have j1 := eq1187 x X1 X0 X1
       grind)
    | exact resolve eq16 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq224797 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have j0 := eq222886 X0 X1
       have j1 := eq56787 x X0 X1 x
       grind)
    | (have r₁ := eq222886 X0 X1
       have r₂ := eq56787 x X1 x y
       grind)
    | exact resolve eq222886 eq56787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56787 eq222886
  have eq225930 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op (σ x) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq138 x x x x X0 X1 X2
       have i₂ := eq224797 (M.op x x) X0
       grind)
    | exact superpose eq224797 eq138
    | exact resolve eq138 eq224797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq262546 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op (M.op X2 X3) X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq883 X2 X3 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq262547 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq262546 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262546
  have eq262556 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq262547 X0 X1 x x
       have i₂ := eq225930 X1 x x
       grind)
    | exact superpose eq225930 eq262547
    | (have j0 := eq262547 X0 X1 x x
       grind)
    | exact resolve eq262547 eq225930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262547
  have eq273943 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ x)) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq154196 X0 (σ x)
       have i₂ := eq262556 X1 X0
       grind)
    | exact superpose eq262556 eq154196
    | (have j0 := eq154196 X0 (σ x)
       have j1 := eq262556 X1 X0
       grind)
    | (have r₁ := eq154196 X1 (σ x)
       have r₂ := eq262556 X0 X1
       grind)
    | exact resolve eq154196 eq262556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154196 eq262556
  have eq274182 : ∀ X0 X1 : G, (k X0 (σ x)) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq273943 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273943
  have eq300359 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) x) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 x
       have i₂ := eq274182 X0 X1
       grind)
    | exact superpose eq274182 eq22
    | (have j1 := eq274182 X0 X1
       grind)
    | exact resolve eq22 eq274182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq274182
  have eq494862 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (k (τ (σ X0)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq300359 (σ X0) (σ X1)
       grind)
    | exact superpose eq300359 eq15
    | (have j1 := eq300359 (σ X0) X1
       grind)
    | exact resolve eq15 eq300359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300359
  have eq494867 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq494862 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq494862
    | (have j0 := eq494862 X0 X1
       grind)
    | exact resolve eq494862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494862
  have eq846524 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq18054 X0 X1 X0 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18054
  have eq846525 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq846524 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846524
  have eq846527 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq846525 X0 X1
       have i₂ := eq224797 X0 X1
       grind)
    | exact superpose eq224797 eq846525
    | exact resolve eq846525 eq224797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224797 eq846525
  have eq846735 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq846527 (σ X0) (σ X0)
       have i₂ := eq226 X0
       grind)
    | exact superpose eq226 eq846527
    | exact resolve eq846527 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq847157 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq846735 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq846735
    | exact resolve eq846735 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846735
  have eq847392 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq847157 X0
       have i₂ := eq846527 X0 X0
       grind)
    | exact superpose eq846527 eq847157
    | exact resolve eq847157 eq846527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846527 eq847157
  have eq962729 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq494867 x y
       grind)
    | exact superpose eq494867 eq16
    | (have j1 := eq494867 x x
       grind)
    | exact resolve eq16 eq494867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494867
  have eq963076 : x = (M.op x x) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq962729
       have i₂ := eq211 x
       grind)
    | exact superpose eq211 eq962729
    | exact resolve eq962729 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq962729
  have eq963140 : x = (M.op x x) := by
    first
    | (have j1 := eq54758 x x
       grind)
    | (have r₁ := eq963076
       have r₂ := eq54758 y x
       grind)
    | exact resolve eq963076 eq54758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54758 eq963076
  have eq963870 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq225930 X0 x x
       have i₂ := eq963140
       grind)
    | exact superpose eq963140 eq225930
    | exact resolve eq225930 eq963140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225930 eq963140
  have eq978047 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq847392 X0
       have i₂ := eq963870 X0
       grind)
    | exact superpose eq963870 eq847392
    | exact resolve eq847392 eq963870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847392
  have eq978074 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq963870 (σ y)
       grind)
    | exact superpose eq963870 eq16
    | exact resolve eq16 eq963870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq978913 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq978047 X0
       have i₂ := eq963870 (σ X0)
       grind)
    | exact superpose eq963870 eq978047
    | exact resolve eq978047 eq963870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963870 eq978047
  have eq1003896 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq978074
       have i₂ := eq978913 y
       grind)
    | exact superpose eq978913 eq978074
    | (have r₁ := eq978074
       have r₂ := eq978913 y
       grind)
    | exact resolve eq978074 eq978913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978074 eq978913
  have eq1004034 : False := by grind
  exact eq1004034

/-- `Equation4433`: `x ◇ (y ◇ x) = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pxy_Equation4433 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4433 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4433.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq89 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq104 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq132 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq104 X0 (τ X1)
       grind)
    | exact superpose eq104 eq20
    | (have j1 := eq104 X0 (τ X1)
       grind)
    | exact resolve eq20 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq104 (σ X0) (σ X1)
       grind)
    | exact superpose eq104 eq15
    | (have j1 := eq104 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq104
  have eq168 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq141 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq169 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq168 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq213 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq169 (σ X0)
       grind)
    | exact superpose eq169 eq15
    | exact resolve eq15 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq213 X0
       have i₂ := eq169 X0
       grind)
    | exact superpose eq169 eq213
    | exact resolve eq213 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq213
  have eq318 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq9
    | exact resolve eq9 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq329 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq321 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq321
    | exact resolve eq321 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq332 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq329
  have eq334 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq332 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq332
    | exact resolve eq332 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq1255 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq318 X0 (σ X0)
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq318
    | exact resolve eq318 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq1282 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1255 X0
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq1255
    | exact resolve eq1255 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq1255
  have eq4259 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq132 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq132
    | exact resolve eq132 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq4400 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4259 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4259
    | (have j0 := eq4259 X0 X1
       grind)
    | exact resolve eq4259 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4259
  have eq6275 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq134 X0 X1
       grind)
    | exact superpose eq134 eq10
    | (have j1 := eq134 X0 X1
       grind)
    | exact resolve eq10 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq6427 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6275 X0 X1
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq6275
    | (have j0 := eq6275 X0 X1
       grind)
    | exact resolve eq6275 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq6275
  have eq6549 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6427 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6427
    | (have j0 := eq6427 X0 X1
       grind)
    | exact resolve eq6427 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6427
  have eq7367 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6549 x y
       grind)
    | exact superpose eq6549 eq16
    | (have j1 := eq6549 x y
       grind)
    | exact resolve eq16 eq6549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6549
  have eq7457 : y = (M.op x x) := by
    first
    | (have j1 := eq4400 y x
       grind)
    | (have r₁ := eq7367
       have r₂ := eq4400 y x
       grind)
    | exact resolve eq7367 eq4400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4400 eq7367
  have eq7945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1282 x
       have i₂ := eq7457
       grind)
    | exact superpose eq7457 eq1282
    | exact resolve eq1282 eq7457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282 eq7457
  have eq7957 : False := by grind
  exact eq7957

/-- `Equation4433`: `x ◇ (y ◇ x) = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pyx_Equation4433 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4433 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4433.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq37 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  clear eq20
  have eq38 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq9 (τ X0) (τ X0)
       grind)
    | exact superpose eq9 eq37
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq89 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq94 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq655 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq89
  have eq8310 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq655 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq8312 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8310 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8310
  have eq8313 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8312 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8312
  have eq8456 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq8313 (σ X0)
       grind)
    | exact superpose eq8313 eq15
    | exact resolve eq15 eq8313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8462 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq8313 (τ X0)
       grind)
    | exact superpose eq8313 eq43
    | exact resolve eq43 eq8313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8469 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8462 X0
       have i₂ := eq8313 X0
       grind)
    | exact superpose eq8313 eq8462
    | exact resolve eq8462 eq8313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8462
  have eq8475 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8456 X0
       have i₂ := eq8313 X0
       grind)
    | exact superpose eq8313 eq8456
    | exact resolve eq8456 eq8313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8313 eq8456
  have eq8905 : ∀ X0 X1 : G, (M.op (τ X0) (M.op X1 (τ X0))) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq8469 X0
       grind)
    | exact superpose eq8469 eq9
    | exact resolve eq9 eq8469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8908 : ∀ X0 : G, (k (τ (M.op X0 X0)) (τ X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    grind
  have eq8997 : ∀ X0 : G, (τ (k (M.op X0 X0) X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq8908 X0
       have i₂ := eq43 X0 (M.op X0 X0)
       grind)
    | exact superpose eq43 eq8908
    | exact resolve eq8908 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq8908
  have eq9022 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    grind
  clear eq8997
  have eq9035 : ∀ X0 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9022 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq9022
    | exact resolve eq9022 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9022
  have eq9552 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq9642 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9552 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq9552
    | exact resolve eq9552 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9552
  have eq9672 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq9642
  have eq9685 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9672 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq9672
    | exact resolve eq9672 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9672
  have eq11811 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq8905 X0 (τ X0)
       grind)
    | exact superpose eq8905 eq38
    | exact resolve eq38 eq8905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq8905
  have eq11859 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11811 X0
       have i₂ := eq9035 X0
       grind)
    | exact superpose eq9035 eq11811
    | exact resolve eq11811 eq9035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9035 eq11811
  have eq11920 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq11859 X0
       have i₂ := eq11 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq11 eq11859
    | exact resolve eq11859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11859
  have eq11948 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (σ (τ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq11920 X0
       have i₂ := eq8469 X0
       grind)
    | exact superpose eq8469 eq11920
    | exact resolve eq11920 eq8469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8469 eq11920
  have eq11970 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11948 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq11948
    | exact resolve eq11948 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11948
  have eq12737 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11970 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq11970 X0
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq11970
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq11970 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12747 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11970 X0
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq11970 X0
       have i₂ := eq94 X0 (M.op X0 X0)
       grind)
    | exact superpose eq94 eq11970
    | (have j1 := eq94 X1 X0
       grind)
    | exact resolve eq11970 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq12808 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12747 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12747
  have eq12812 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12737 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12737
  have eq14929 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11970 X0
       have i₂ := eq12812 X0 X1
       grind)
    | (have i₁ := eq11970 X0
       have i₂ := eq12812 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12812 eq11970
    | (have j1 := eq12812 X0 X1
       grind)
    | exact resolve eq11970 eq12812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11970
  have eq14965 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8475 X1
       have i₂ := eq12812 (σ X1) X0
       grind)
    | (have i₁ := eq8475 X0
       have i₂ := eq12812 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12812 eq8475
    | (have j1 := eq12812 (σ X1) X0
       grind)
    | exact resolve eq8475 eq12812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8475
  have eq22891 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12808 X0 X1
       have i₂ := eq14929 X0 X1
       grind)
    | exact superpose eq14929 eq12808
    | (have j0 := eq12808 X0 X1
       have j1 := eq14929 X0 X1
       grind)
    | exact resolve eq12808 eq14929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12808 eq14929
  have eq22924 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq22891 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22891
  have eq27203 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq14965 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq14965 (σ X0) X1
       grind)
    | exact superpose eq14965 eq10
    | (have j1 := eq14965 X0 X1
       grind)
    | exact resolve eq10 eq14965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14965
  have eq31329 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq27203 (σ X0) X1
       grind)
    | exact superpose eq27203 eq15
    | (have j1 := eq27203 (σ X0) X1
       grind)
    | exact resolve eq15 eq27203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27203
  have eq31390 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31329 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31329
    | (have j0 := eq31329 X0 X1
       grind)
    | exact resolve eq31329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31329
  have eq37087 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31390 x y
       grind)
    | exact superpose eq31390 eq16
    | (have j1 := eq31390 x y
       grind)
    | exact resolve eq16 eq31390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31390
  have eq38650 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq37087
       have i₂ := eq12812 y x
       grind)
    | exact superpose eq12812 eq37087
    | (have j1 := eq12812 y x
       grind)
    | exact resolve eq37087 eq12812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12812 eq37087
  have eq38661 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq38650
  have eq38662 : x = (M.op y y) := by grind
  clear eq38661
  have eq39288 : (M.op x y) = (k x y) := by grind
  have eq39320 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq9685 y
       have i₂ := eq38662
       grind)
    | exact superpose eq38662 eq9685
    | exact resolve eq9685 eq38662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9685 eq38662
  have eq40290 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq22924 x y
       have i₂ := eq39288
       grind)
    | exact superpose eq39288 eq22924
    | (have j0 := eq22924 y x
       grind)
    | exact resolve eq22924 eq39288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22924 eq39288
  have eq40291 : (M.op x y) = (M.op y x) := by grind
  clear eq40290
  have eq48723 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39320
       grind)
    | exact superpose eq39320 eq16
    | exact resolve eq16 eq39320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39320
  have eq48768 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq48723
       have i₂ := eq40291
       grind)
    | exact superpose eq40291 eq48723
    | exact resolve eq48723 eq40291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40291 eq48723
  have eq48769 : False := by grind
  exact eq48769

/-- `Equation4433`: `x ◇ (y ◇ x) = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pxy_Equation4433 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4433 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4433.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq87 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq96 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq653 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq87
  have eq1729 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq98 X1 X0
       grind)
    | exact superpose eq98 eq10
    | (have j1 := eq98 X1 X0
       grind)
    | exact resolve eq10 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq8419 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq653 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq8421 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8419 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8419
  have eq8422 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8421 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8421
  have eq8560 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq8422 (σ X0)
       grind)
    | exact superpose eq8422 eq15
    | exact resolve eq15 eq8422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8579 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8560 X0
       have i₂ := eq8422 X0
       grind)
    | exact superpose eq8422 eq8560
    | exact resolve eq8560 eq8422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8422 eq8560
  have eq9541 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq8579 X0
       grind)
    | exact superpose eq8579 eq9
    | exact resolve eq9 eq8579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9544 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq9637 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9544 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq9544
    | exact resolve eq9544 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9544
  have eq9666 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq9637
  have eq9852 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq10264 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9852 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq9852
    | (have j0 := eq9852 X0 X1
       grind)
    | exact resolve eq9852 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9852
  have eq13572 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9541 X0 (σ X0)
       have i₂ := eq8579 X0
       grind)
    | exact superpose eq8579 eq9541
    | exact resolve eq9541 eq8579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9541
  have eq13648 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13572 X0
       have i₂ := eq9666 X0
       grind)
    | exact superpose eq9666 eq13572
    | exact resolve eq13572 eq9666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13572
  have eq52517 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq1729 X1 X0
       grind)
    | exact superpose eq1729 eq10
    | (have j1 := eq1729 X1 X0
       grind)
    | exact resolve eq10 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729
  have eq53003 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52517 X0 X1
       have i₂ := eq8579 X0
       grind)
    | exact superpose eq8579 eq52517
    | (have j0 := eq52517 X0 X1
       grind)
    | exact resolve eq52517 eq8579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52517
  have eq53637 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53003 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq53003
    | (have j0 := eq53003 X0 X1
       grind)
    | exact resolve eq53003 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53003
  have eq54160 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53637 X0 X1
       have i₂ := eq8579 X1
       grind)
    | exact superpose eq8579 eq53637
    | (have j0 := eq53637 X0 X1
       grind)
    | exact resolve eq53637 eq8579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8579 eq53637
  have eq54537 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54160 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq54160
    | (have j0 := eq54160 X0 X1
       grind)
    | exact resolve eq54160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54160
  have eq122735 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54537 x y
       grind)
    | exact superpose eq54537 eq16
    | (have j1 := eq54537 x y
       grind)
    | exact resolve eq16 eq54537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54537
  have eq123261 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq10264 x y
       grind)
    | (have r₁ := eq122735
       have r₂ := eq10264 y x
       grind)
    | exact resolve eq122735 eq10264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10264 eq122735
  have eq125801 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op x X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 y X0
       have i₂ := eq123261
       grind)
    | exact superpose eq123261 eq9
    | exact resolve eq9 eq123261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125852 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13648 y
       have i₂ := eq123261
       grind)
    | exact superpose eq123261 eq13648
    | exact resolve eq13648 eq123261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13648
  have eq130298 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq125801 y
       have i₂ := eq123261
       grind)
    | exact superpose eq123261 eq125801
    | exact resolve eq125801 eq123261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123261 eq125801
  have eq130368 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq130298
  have eq134279 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq125852
       grind)
    | exact superpose eq125852 eq16
    | exact resolve eq16 eq125852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125852
  have eq134717 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq134279
       have i₂ := eq130368
       grind)
    | exact superpose eq130368 eq134279
    | exact resolve eq134279 eq130368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130368 eq134279
  have eq134718 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq134717
  have eq134719 : y = (M.op x x) := by grind
  clear eq134718
  have eq135421 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9666 x
       have i₂ := eq134719
       grind)
    | exact superpose eq134719 eq9666
    | exact resolve eq9666 eq134719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9666 eq134719
  have eq135521 : False := by grind
  exact eq135521

/-- `Equation4434`: `x ◇ (y ◇ x) = (x ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pxy_Equation4434 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X0 X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X0 x X3
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X0 X0))) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X0) X2 X3
       have i₂ := eq9 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2 (M.op x (M.op X0 X0))
       have i₂ := eq9 (M.op X0 X0) x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X2) = (k (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X0) X2
       have i₂ := eq9 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 X0) X2
       grind)
    | exact resolve eq12 eq9
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
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
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
  have eq70 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
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
  have eq78 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq70 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq79 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq84 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq78 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq78 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq78 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq85 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq79 X0 X1 X1
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq79 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq79 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq79 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq86 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq68 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq68 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq68 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq128 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X0 X0) X3
       have i₂ := eq25 X0 X2 X1
       grind)
    | (have i₁ := eq9 X2 (M.op X0 X0) X3
       have i₂ := eq25 X0 X1 X2
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X2 X3 (M.op X0 X0)
       have i₂ := eq25 X0 X2 X1
       grind)
    | (have i₁ := eq28 X2 X3 (M.op X0 X0)
       have i₂ := eq25 X0 X1 X2
       grind)
    | exact superpose eq25 eq28
    | exact resolve eq28 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X2 X3 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq28
    | exact resolve eq28 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op X0 (M.op X4 (M.op X5 X4))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq24 X4 X5 X0 x
       have i₂ := eq24 X1 X2 X0 x
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) X3) = (M.op X2 (M.op X4 (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X4 (M.op X0 X0) X2 X3
       have i₂ := eq25 X0 X4 X1
       grind)
    | (have i₁ := eq24 X4 (M.op X0 X0) X2 X3
       have i₂ := eq25 X0 X1 X4
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 X3)) = (M.op X3 (M.op X0 (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq28 X3 (M.op X0 X0) X4
       have i₂ := eq128 X1 X2 X0 X3
       grind)
    | exact superpose eq128 eq28
    | exact resolve eq28 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq355 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq84 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq356 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq355 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq360 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq356 (σ X0)
       grind)
    | exact superpose eq356 eq15
    | exact resolve eq15 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0 X0
       have i₂ := eq356 (τ X0)
       grind)
    | exact superpose eq356 eq39
    | exact resolve eq39 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq369 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq362 X0
       have i₂ := eq356 X0
       grind)
    | exact superpose eq356 eq362
    | exact resolve eq362 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq371 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq360 X0
       have i₂ := eq356 X0
       grind)
    | exact superpose eq356 eq360
    | exact resolve eq360 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq412 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = X0 ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X0
       have i₂ := eq86 X0 X1 X3
       grind)
    | (have i₁ := eq14 X0 X1
       have i₂ := eq86 X1 X1 X2
       grind)
    | exact superpose eq86 eq14
    | (have j0 := eq14 X2 X2
       have j1 := eq86 X0 X1 X2
       grind)
    | exact resolve eq14 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = X0 ∨ (M.op X2 X0) = (k X2 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq412 X0 X1 X2 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq412 X0 X0 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq412 X0 X1 X0 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq412 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq464 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) x
       have i₂ := eq371 X0
       grind)
    | exact superpose eq371 eq9
    | exact resolve eq9 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq371 X0
       grind)
    | exact superpose eq371 eq9
    | exact resolve eq9 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29 X0 X3 X2
       have i₂ := eq25 X0 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq29 X0 X3 X2
       have i₂ := eq25 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq25 eq29
    | exact resolve eq29 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : ∀ X0 X1 X2 : G, (M.op (τ X0) (M.op X1 (τ X0))) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X1 X2
       have i₂ := eq369 X0
       grind)
    | exact superpose eq369 eq9
    | exact resolve eq9 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X5 X3)) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 X1))) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq160 (M.op X0 X0) X4 X3 X5
       have i₂ := eq24 X1 X2 X0 (M.op X0 X0)
       grind)
    | exact superpose eq24 eq160
    | exact resolve eq160 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq719 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X3 X1)) = (M.op X1 (M.op (τ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq160 (τ X0) X2 X1 X3
       have i₂ := eq369 X0
       grind)
    | exact superpose eq369 eq160
    | exact resolve eq160 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1182 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X3) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X0 X3 (M.op x (M.op X0 X0))
       have i₂ := eq27 X0 X1 x X2
       grind)
    | exact superpose eq27 eq25
    | exact resolve eq25 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1184 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op X0 (M.op (M.op X4 X4) X5)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq128 X4 X5 X0 (M.op x (M.op X0 X0))
       have i₂ := eq27 X0 X1 x X2
       grind)
    | exact superpose eq27 eq128
    | exact resolve eq128 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1387 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X3) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq128 x X0 X0 X3
       have i₂ := eq516 X0 X1 (M.op x x) X2
       grind)
    | exact superpose eq516 eq128
    | exact resolve eq128 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq516
  have eq1504 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X2) = X0 ∨ (M.op X3 X2) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq85 X2 X0 X3
       grind)
    | exact superpose eq85 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq85 X2 X0 X3
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq85 X0 X1 X2
       grind)
    | exact resolve eq12 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1553 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X2) = X0 ∨ (M.op X3 X2) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1504 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq2475 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X0) X3) = (M.op (M.op X0 (M.op X1 (M.op X2 X1))) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq1182 X0 x X5 X3
       have i₂ := eq161 X1 X2 X0 x
       grind)
    | (have i₁ := eq1182 (M.op X1 X0) X0 X2 X3
       have i₂ := eq161 X0 X1 (M.op X1 X0) X3
       grind)
    | exact superpose eq161 eq1182
    | exact resolve eq1182 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq1182
  have eq3123 : ∀ X0 X2 X3 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X2) = (k (M.op X0 X0) X2) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq38 X0 x X2
       have i₂ := eq86 X0 (M.op x X0) X3
       grind)
    | exact superpose eq86 eq38
    | (have j0 := eq38 X0 x X2
       have j1 := eq86 X2 x (M.op X0 X0)
       grind)
    | (have r₁ := eq38 X0 x X2
       have r₂ := eq86 X0 (M.op x X0) X2
       grind)
    | exact resolve eq38 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq86
  have eq3140 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X0) X2) = (k (M.op X0 X0) X2) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X2 X3
    first
    | (have j0 := eq3123 X0 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3123
  have eq5793 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X0) X1)) X2) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq464 (M.op X0 X0) X1
       have i₂ := eq25 X0 (M.op X0 X0) x
       grind)
    | (have i₁ := eq464 (M.op X0 X0) X1
       have i₂ := eq25 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq25 eq464
    | exact resolve eq464 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6004 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X0) X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5793 X0 X1 X2
       have i₂ := eq464 X0 (σ (M.op (M.op X0 X0) X1))
       grind)
    | exact superpose eq464 eq5793
    | exact resolve eq5793 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5793
  have eq10320 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op X1 (M.op (τ (τ (M.op X0 X0))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq719 (τ X0) X1 X3 X2
       have i₂ := eq369 X0
       grind)
    | exact superpose eq369 eq719
    | exact resolve eq719 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq39626 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq3140 X0 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3140
  have eq39627 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq39626 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39626
  have eq39719 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39627 (σ X0)
       have i₂ := eq371 X0
       grind)
    | exact superpose eq371 eq39627
    | exact resolve eq39627 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq39750 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq39719 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq39719
    | exact resolve eq39719 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39719
  have eq39760 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39750 X0
       have i₂ := eq39627 X0
       grind)
    | exact superpose eq39627 eq39750
    | exact resolve eq39750 eq39627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39627 eq39750
  have eq39768 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq39760 X0
       have i₂ := eq464 X0 (σ X0)
       grind)
    | exact superpose eq464 eq39760
    | exact resolve eq39760 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39760
  have eq41538 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) X1))) = (σ (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39768 (M.op X0 X0)
       have i₂ := eq25 X0 (M.op X0 X0) x
       grind)
    | (have i₁ := eq39768 (M.op X0 X0)
       have i₂ := eq25 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq25 eq39768
    | exact resolve eq39768 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41610 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X1
       have i₂ := eq39768 X0
       grind)
    | exact superpose eq39768 eq464
    | exact resolve eq464 eq39768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41749 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq41538 X0 X1
       have i₂ := eq464 X0 (σ (M.op (M.op X0 X0) X1))
       grind)
    | exact superpose eq464 eq41538
    | exact resolve eq41538 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq41538
  have eq41816 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq41749 X0 X1
       have i₂ := eq39768 X0
       grind)
    | exact superpose eq39768 eq41749
    | exact resolve eq41749 eq39768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41749
  have eq43582 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (σ (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41610 X0 X2
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq41610
    | exact resolve eq41610 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43585 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41610 X0 X2
       have i₂ := eq25 X0 X0 X1
       grind)
    | (have i₁ := eq41610 X0 X2
       have i₂ := eq25 X0 X1 X0
       grind)
    | exact superpose eq25 eq41610
    | exact resolve eq41610 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq43613 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) X2) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41610 (M.op X0 X0) X2
       have i₂ := eq1387 X0 (M.op X0 X0) (M.op X0 X0) X1
       grind)
    | exact superpose eq1387 eq41610
    | exact resolve eq41610 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387 eq41610
  have eq44031 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43613 X0 X1 x
       have i₂ := eq6004 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq6004 eq43613
    | exact resolve eq43613 eq6004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6004 eq43613
  have eq45664 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X0 (M.op X1 X0))) X2) = (σ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X3 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq43582 (M.op (M.op X0 X0) (M.op X0 X0)) X3 X2
       have i₂ := eq29 X0 (M.op (M.op X0 X0) (M.op X0 X0)) X1
       grind)
    | exact superpose eq29 eq43582
    | exact resolve eq43582 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46349 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (τ (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 (M.op X2 X0))
       have i₂ := eq43582 X0 X2 X1
       grind)
    | exact superpose eq43582 eq10
    | exact resolve eq10 eq43582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43582
  have eq46564 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 (M.op X1 X0))) X2) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45664 X0 X1 X2 x
       have i₂ := eq44031 (M.op X0 X0) (M.op x (M.op (M.op X0 X0) (M.op X0 X0)))
       grind)
    | exact superpose eq44031 eq45664
    | exact resolve eq45664 eq44031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44031 eq45664
  have eq46628 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 (M.op X1 X0))) X2) = (σ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46564 X0 X1 X2
       have i₂ := eq39768 (M.op X0 X0)
       grind)
    | exact superpose eq39768 eq46564
    | exact resolve eq46564 eq39768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39768 eq46564
  have eq46644 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 (M.op X1 X0))) X2) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46628 X0 X1 X2
       have i₂ := eq41816 X0 (M.op X0 X0)
       grind)
    | exact superpose eq41816 eq46628
    | exact resolve eq46628 eq41816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41816 eq46628
  have eq48348 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X2 (σ X0))) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq465 X0 X2 x
       have i₂ := eq43585 X0 X1 x
       grind)
    | exact superpose eq43585 eq465
    | exact resolve eq465 eq43585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465 eq43585
  have eq53226 : ∀ X0 X1 X3 : G, (M.op (τ (M.op X0 X0)) X3) = (τ (M.op (σ (M.op (τ X0) (τ X0))) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq596 X0 x X3
       have i₂ := eq46349 (τ X0) X1 x
       grind)
    | exact superpose eq46349 eq596
    | exact resolve eq596 eq46349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq46349
  have eq53273 : ∀ X0 X1 X3 : G, (M.op (τ (M.op X0 X0)) X3) = (τ (M.op (σ (τ (M.op X0 X0))) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53226 X0 X1 X3
       have i₂ := eq369 X0
       grind)
    | exact superpose eq369 eq53226
    | exact resolve eq53226 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq53226
  have eq53477 : ∀ X0 X1 X3 : G, (M.op (τ (M.op X0 X0)) X3) = (τ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53273 X0 X1 X3
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq53273
    | exact resolve eq53273 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53273
  have eq58005 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X2) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq451 X1 X2 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq58006 : ∀ X0 X1 X2 : G, (M.op X1 X2) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq58005 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58005
  have eq58588 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq58006 (τ X0) X1 X2
       grind)
    | exact superpose eq58006 eq17
    | (have j1 := eq58006 X0 X1 X2
       grind)
    | exact resolve eq17 eq58006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq65756 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) X2) = (τ (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53477 X0 x X2
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq53477
    | exact resolve eq53477 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53477
  have eq66625 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1553 X0 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq66627 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq66625 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66625
  have eq66672 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq66627 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66627
  have eq67470 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66672 X0 X1
       have i₂ := eq58006 X2 X0 X1
       grind)
    | exact superpose eq58006 eq66672
    | (have j0 := eq66672 X0 X1
       have j1 := eq58006 X2 X0 X2
       grind)
    | (have r₁ := eq66672 X1 X2
       have r₂ := eq58006 X0 X1 X2
       grind)
    | exact resolve eq66672 eq58006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58006
  have eq67503 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 X0)) ≠ (M.op X0 (M.op (M.op X1 X1) X2)) ∨ (M.op X0 (M.op X3 X0)) = (k (M.op X0 (M.op X3 X0)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq66672 (M.op X0 (M.op X3 X0)) X4
       have i₂ := eq1184 X0 X3 X4 X1 X2
       grind)
    | exact superpose eq1184 eq66672
    | (have j0 := eq66672 (M.op X0 (M.op X3 X0)) X4
       grind)
    | (have r₁ := eq66672 (M.op x (M.op (M.op X4 X4) x)) X2
       have r₂ := eq1184 x (M.op X4 X4) X2 X4 x
       grind)
    | exact resolve eq66672 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184 eq66672
  have eq67561 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq67470 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67470
  have eq67614 : ∀ X0 X3 X4 : G, (M.op X0 (M.op X3 X0)) = (k (M.op X0 (M.op X3 X0)) X4) := by
    intro X0 X3 X4
    first
    | (have j0 := eq67503 X0 x x X3 X4
       grind)
    | (have r₁ := eq67503 x x x (M.op X0 X0) X4
       have r₂ := eq160 X0 x x (M.op x x)
       grind)
    | (have r₁ := eq67503 x X0 x X3 X4
       have r₂ := eq160 X0 x x X3
       grind)
    | exact resolve eq67503 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq67503
  have eq68575 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq67561 X0 (σ X1) X2
       grind)
    | exact superpose eq67561 eq22
    | (have j1 := eq67561 (τ X0) X1 X2
       grind)
    | exact resolve eq22 eq67561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq67561
  have eq80711 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op X2 (τ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq202 x x X2 X3 (τ (M.op X0 X0))
       have i₂ := eq65756 X0 X1 (M.op (M.op x x) x)
       grind)
    | exact superpose eq65756 eq202
    | exact resolve eq202 eq65756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq80715 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X2 (τ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq306 (τ (M.op X0 X0)) x x X2 X3
       have i₂ := eq65756 X0 X1 (M.op (M.op x x) x)
       grind)
    | exact superpose eq65756 eq306
    | exact resolve eq306 eq65756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq65756
  have eq104796 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X1)) = (k (τ (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq68575 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq68575 eq15
    | (have j1 := eq68575 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq68575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68575
  have eq104816 : ∀ X0 X1 X2 : G, (k X1 X2) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104796 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq104796
    | (have j0 := eq104796 X0 X1 X2
       grind)
    | exact resolve eq104796 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104796
  have eq308197 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58588 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58588
    | (have j0 := eq58588 X0 X1 X2
       grind)
    | exact resolve eq58588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58588
  have eq310034 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq308197 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq308197
    | (have j0 := eq308197 X0 X1 X2
       grind)
    | exact resolve eq308197 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308197
  have eq313540 : ∀ X0 X2 X3 : G, (k X0 X2) = X0 ∨ (σ (k X3 X0)) = (σ (M.op X3 X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq67614 x X3 x
       have i₂ := eq310034 X0 x (M.op X3 x)
       grind)
    | exact superpose eq310034 eq67614
    | (have j1 := eq310034 X3 X0 X2
       grind)
    | exact resolve eq67614 eq310034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67614 eq310034
  have eq411216 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq104816 x y X0
       grind)
    | exact superpose eq104816 eq16
    | (have j1 := eq104816 X0 y X0
       grind)
    | exact resolve eq16 eq104816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104816
  have eq411231 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have j0 := eq411216 X0
       have j1 := eq313540 y X0 x
       grind)
    | (have r₁ := eq411216 X0
       have r₂ := eq313540 y x x
       grind)
    | exact resolve eq411216 eq313540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313540 eq411216
  have eq411715 : y = (M.op y y) := by
    first
    | (have i₁ := eq356 y
       have i₂ := eq411231 y
       grind)
    | exact superpose eq411231 eq356
    | exact resolve eq356 eq411231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq411231
  have eq412500 : ∀ X0 : G, (M.op y y) = (M.op (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq29 y x y
       have i₂ := eq411715
       grind)
    | exact superpose eq411715 eq29
    | exact resolve eq29 eq411715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq412516 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op X0 (M.op y y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq184 X0 X1 X2 y y
       have i₂ := eq411715
       grind)
    | exact superpose eq411715 eq184
    | exact resolve eq184 eq411715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq412543 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X2 (M.op y y)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq713 X2 y y X0 X3 X1
       have i₂ := eq411715
       grind)
    | exact superpose eq411715 eq713
    | exact resolve eq713 eq411715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq412567 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 (M.op y y)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2475 X0 y y X1 X2
       have i₂ := eq411715
       grind)
    | exact superpose eq411715 eq2475
    | exact resolve eq2475 eq411715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2475
  have eq412589 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq46644 y y x
       have i₂ := eq411715
       grind)
    | exact superpose eq411715 eq46644
    | exact resolve eq46644 eq411715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46644
  have eq412612 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (τ (M.op y y))) := by
    intro X0 X1
    first
    | (have i₁ := eq80711 y y X0 X1
       have i₂ := eq411715
       grind)
    | exact superpose eq411715 eq80711
    | exact resolve eq80711 eq411715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80711
  have eq412613 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (τ (M.op y y))) := by
    intro X0 X1
    first
    | (have i₁ := eq80715 y y X0 X1
       have i₂ := eq411715
       grind)
    | exact superpose eq411715 eq80715
    | exact resolve eq80715 eq411715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80715
  have eq412619 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (τ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq412613 X0 X1
       have i₂ := eq411715
       grind)
    | exact superpose eq411715 eq412613
    | exact resolve eq412613 eq411715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412613
  have eq412620 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (τ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq412612 X0 X1
       have i₂ := eq411715
       grind)
    | exact superpose eq411715 eq412612
    | exact resolve eq412612 eq411715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412612
  have eq412639 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq412589 X0
       have i₂ := eq411715
       grind)
    | exact superpose eq411715 eq412589
    | exact resolve eq412589 eq411715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412589
  have eq412653 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq412567 X0 X1 X2
       have i₂ := eq411715
       grind)
    | exact superpose eq411715 eq412567
    | exact resolve eq412567 eq411715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412567
  have eq412664 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X2 y) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq412543 X0 X1 X2 X3
       have i₂ := eq411715
       grind)
    | exact superpose eq411715 eq412543
    | exact resolve eq412543 eq411715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412543
  have eq412677 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq412516 X0 X1 X2
       have i₂ := eq411715
       grind)
    | exact superpose eq411715 eq412516
    | exact resolve eq412516 eq411715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412516
  have eq412681 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq412500 X0
       have i₂ := eq411715
       grind)
    | exact superpose eq411715 eq412500
    | exact resolve eq412500 eq411715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411715 eq412500
  have eq412717 : ∀ X0 X2 : G, (M.op X0 (τ y)) = (M.op (M.op X0 y) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq412653 X0 x X2
       have i₂ := eq412620 X0 x
       grind)
    | exact superpose eq412620 eq412653
    | exact resolve eq412653 eq412620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412653
  have eq412723 : ∀ X0 X2 X3 : G, (M.op X0 (τ y)) = (M.op X0 (M.op (M.op X2 y) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq412664 X0 x X2 X3
       have i₂ := eq412619 X0 x
       grind)
    | exact superpose eq412619 eq412664
    | exact resolve eq412664 eq412619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412664
  have eq412731 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 (τ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq412677 X0 X1 x
       have i₂ := eq412619 X1 x
       grind)
    | exact superpose eq412619 eq412677
    | exact resolve eq412677 eq412619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412619 eq412677
  have eq412740 : ∀ X0 X2 : G, (M.op X0 (τ y)) = (M.op X0 (M.op X2 (τ y))) := by
    intro X0 X2
    first
    | (have i₁ := eq412723 X0 X2 x
       have i₂ := eq412717 X2 x
       grind)
    | exact superpose eq412717 eq412723
    | exact resolve eq412723 eq412717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412717 eq412723
  have eq412745 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq412740 X0 x
       have i₂ := eq412731 X0 x
       grind)
    | exact superpose eq412731 eq412740
    | exact resolve eq412740 eq412731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412731 eq412740
  have eq413766 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (τ (τ (M.op X1 X1))) X2)) = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10320 X1 X0 y X2
       have i₂ := eq412681 X0
       grind)
    | exact superpose eq412681 eq10320
    | exact resolve eq10320 eq412681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414091 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X1)) = (M.op (σ X0) y) := by
    intro X0 X1
    first
    | (have i₁ := eq48348 X0 X1 y
       have i₂ := eq412681 (σ X0)
       grind)
    | exact superpose eq412681 eq48348
    | exact resolve eq48348 eq412681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48348 eq412681
  have eq414132 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 (τ y))) := by
    intro X0
    first
    | (have i₁ := eq414091 X0 x
       have i₂ := eq412620 X0 x
       grind)
    | exact superpose eq412620 eq414091
    | exact resolve eq414091 eq412620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412620 eq414091
  have eq414317 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq414132 X0
       have i₂ := eq412745 X0
       grind)
    | exact superpose eq412745 eq414132
    | exact resolve eq414132 eq412745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412745 eq414132
  have eq424102 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (τ (τ (M.op X1 X1))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10320 X1 X0 (σ y) X2
       have i₂ := eq412639 X0
       grind)
    | exact superpose eq412639 eq10320
    | exact resolve eq10320 eq412639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10320 eq412639
  have eq424641 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq424102 X0 x x
       have i₂ := eq413766 X0 x x
       grind)
    | exact superpose eq413766 eq424102
    | exact resolve eq424102 eq413766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413766 eq424102
  have eq433262 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq424641 (σ x)
       grind)
    | exact superpose eq424641 eq16
    | exact resolve eq16 eq424641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424641
  have eq433347 : False := by grind
  exact eq433347
